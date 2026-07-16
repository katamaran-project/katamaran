---
name: cfgver-wp2
description: >
  Binary WP2 semantics mechanics for Katamaran adequacy proofs:
  semWP2_unfold / semWP2_fix, stm_to_val, IVal (inl success / inr failure), the four
  terminal-case reductions, Result2 in BinaryAdequacy.v, and the Is_true vs "= true"
  syntactic mismatch. Library skill — normally loaded via cfgver-soundness or
  cfgver-endtoend; consult directly when a semWP2 or adequacy proof is stuck on an
  unreduced match after rewrite semWP2_unfold, env.drop_cat terms, an iMod that cannot
  eliminate a "modality match i with inl/inr", or a val-cross-fail bullet. NOT for the
  high-level soundness chain (cfgver-soundness).
---

# Binary WP2 semantics (`semWP2_unfold`) — proof mechanics

Step-level reference for proofs that unfold the binary weakest precondition. The
chain-level picture (why these proofs exist, what they feed) is in **cfgver-soundness**.

## Core definitions

`IVal τ = Val τ + string` — `inl v` is a success value, `inr m` is a failure string.

`stm_to_val` maps `stm_val _ v ↦ Some(inl v)`, `stm_fail _ m ↦ Some(inr m)`, and all
non-terminal statements to `None`.

## The four terminal cases

`semWP2_fix` / `semWP2_unfold` distinguish:

| `stm_to_val s1` | `stm_to_val s2` | Result |
|-----------------|-----------------|--------|
| `Some(inl v1)` | `Some(inl v2)` | `POST (inl v1) δ1 (inl v2) δ2` |
| `Some(inr m1)` | `Some(inr m2)` | `POST (inr m1) δ1 (inr m2) δ2` |
| mixed (inl×inr or inr×inl) | — | `\|={⊤}=> False` |
| `None` (either side) | — | stepping cases |

`Result2` in `BinaryAdequacy.v` has the same structure: `Some(inl)×Some(inl)` and
`Some(inr)×Some(inr)` call POST; everything else reduces to `False`.

## Proof consequences

- When **both** sides are concrete constructors (`stm_val`/`stm_fail`), `cbn` after
  `rewrite semWP2_unfold` immediately reduces to the correct branch — **no
  `env.drop_cat` terms appear**. If `rewrite !env.drop_cat` then fails for a val×fail
  or fail×val bullet, that is why: the match already collapsed to `|={⊤}=> False`.
  Close with `do 3 iModIntro. iMod "Hclose". iMod "WPk". auto.`
- When one side is an **abstract** stepping statement, partial match arms with
  `env.drop` terms remain visible — that is when the `env.drop_cat` rewrites apply.
- `iMod "H"` failing with "cannot eliminate modality match i with inl/inr": after
  `case_match` introduces an abstract `i : IVal τ`, the hypothesis is a `match`, and
  Iris needs a syntactic `|={E}=> P`. Add `destruct i as [v2|m2].` first.
- In `semWP2_call_frame`-style proofs, the val×step / step×val `stm_fail` sub-case
  produces `WPs : |={⊤}=> False`, which `try solve [… iMod "WPs"; auto]` closes
  immediately — a trailing `{ inversion H. }` for those cases hits "No such goal".
  Keep it only for fail×step / step×fail where `inr×inr` gives POST.
- `Is_true b` (from coercion) is NOT syntactically `b = true`; Iris tactics match
  syntactically. Convert with `cbn; rewrite Hexit; exact I` or align both sides.
