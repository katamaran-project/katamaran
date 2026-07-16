---
name: iris-proofmode
description: >
  Iris Proof Mode (IPM) reference for separation-logic proofs in Rocq. Use when
  writing or debugging Iris proofs: iApply / iExact / iFrame / iMod / iDestruct /
  iIntros / iPoseProof failures, wand (-∗) and separating-conjunction (∗) goals,
  fancy updates (|={E}=>), persistent (#) vs spatial hypotheses, pure embeddings
  (⌜P⌝), big_sepM/big_sepL access, or Löb/iInduction structure. Typical symptoms:
  "iApply fails despite terms looking equal", "No such goal after iFrame", "iMod
  cannot eliminate modality", residual |={⊤}=> True. NOT for Katamaran's binary WP2
  specifics (cfgver-wp2), the CFGVer wiring proofs (cfgver-endtoend-internals), or
  plain non-Iris Rocq (rocq skill).
---

# Iris Proof Mode — working reference

Generic IPM knowledge, seeded with pitfalls hit in this codebase. Katamaran-binary
specifics (RelVal, semWP2 terminal cases) live in **cfgver-wp2**.

## The one principle behind half the failures

**IPM tactics match syntactically, not up to conversion.** `iApply`, `iExact`,
`iFrame`, and `iMod` unify against the goal's literal syntax; definitional equality
is not enough. Consequences:

- `Is_true b` (coercion) vs `b = true`: NOT interchangeable for `iApply`/`iExact`
  even though logically equivalent. Convert first (`cbn; rewrite Hexit; exact I`)
  or state both sides in the same form.
- `iApply H` "cannot apply": IPM does not unfold `Definition`s to discover a `-∗`
  inside. Either `unfold the_definition.` first or `iPoseProof (H with "[...]") as
  "H'"` and continue from the exposed shape.
- `iMod "H"` "cannot eliminate modality `match i with inl … | inr … end`": the
  hypothesis must be a *syntactic* `|={E}=> P`. If a `case_match`/abstract scrutinee
  hides the modality under a `match`, `destruct i as [v|m].` first.

## Contexts: spatial vs intuitionistic

`iIntros "(H1 & H2 & #Hinv)"` — `#` puts `Hinv` in the intuitionistic (persistent)
context: it survives splitting and can be used any number of times. Spatial
hypotheses are owned once. `iFrame "∗ #"` frames from both contexts.

Entering a sub-proof with an *empty* spatial context (e.g. a higher-order premise
like an `ImplPre` argument) means outer spatial hypotheses are invisible inside —
if the sub-proof needs a resource, it must be threaded through the premise's domain
(this is why `_with_mem` lemma variants exist in this codebase).

## `iFrame` behavior worth knowing

- `iFrame` **auto-closes** goals that become `True`/`emp`. A trailing `done.` then
  fails with "No such goal" — delete it, iFrame already finished.
- Framing order in one call: named hypotheses first, then contexts —
  `iFrame "Hmem ∗ #"`.
- The **double-iFrame idiom**: `iFrame "∗ #". by iFrame "∗ #".` — the first pass
  frames what it can; the second closes the residual (common after `iApply`ing a
  lemma whose conclusion re-mentions framed resources). A missing second call often
  surfaces later as a confusing "Wrong bullet" error.

## Fancy updates

- Applying a lemma through a `|={⊤}=>` goal can succeed but leave a trivial
  `|={⊤}=> True` side goal — close with `done.`
- Introduce a plain update with `iModIntro`; strip one with `iMod "H"` (subject to
  the syntactic-shape rule above).

## Typeclass arguments (`gFunctors`)

For a hypothesis `H : forall `{sailGS2 Σ}, P`, use `iApply H.` with **no**
argument — the ambient Iris instance fixes `Σ`. `iApply (H Σ')` fails with
"expected gFunctors": the visible binder wants the functor, not the instance.

## Big separating conjunctions

`[∗ map]` / `[∗ list]` ownership is accessed one entry at a time with the
`_lookup_acc` lemmas, e.g.

```coq
iDestruct (big_sepM_lookup_acc _ _ k Hlk with "Hmap") as "[Hk Hclose]".
(* use Hk …, then give it back: *)
iSpecialize ("Hclose" with "Hk").
```

The give-back wand (`Hclose`) restores the full big-op — don't drop it if the
big-op is needed again (in an affine logic dropping is silent, not an error).

## Structural tactics quick reference

| Goal shape | Tactic |
|---|---|
| `P ∗ Q` (split resources) | `iSplitL "H1 H2"` / `iSplitR "H3"` (name who gets what) |
| `P ∧ Q` | `iSplit` (both sides get everything) |
| `⌜φ⌝` | `iPureIntro` |
| `∃ x, Φ x` | `iExists v` |
| `P -∗ Q` in a hypothesis | `iApply ("H" with "[$]")` / `iSpecialize` |
| guarded recursion / loops | `iLöb as "IH"` or `iInduction n as [|n] "IH"` |

Inside `iInduction`'s `-` bullets, deeper case splits need different bullet symbols
(`+`, `--`, `*`) — Rocq bullet discipline applies to IPM proofs unchanged.
