---
name: secret-data-walls
description: >
  The observation boundary in Katamaran's relational verifier: secret (NonSyncVal)
  data is fine as a VALUE but collapses to False the moment it reaches a formula or
  secLeak — `formula_bool`, `formula_relop`, and `secLeak` all map NonSyncVal ⇒
  False (Formulas.v). Explains why `term_eq`/`relop` on secret data is safe as a
  value yet fatal as a branch / path / publicness condition, and why canonical forms
  for secret computations should stay in pure `bv` arithmetic (no relop, no bool) to
  be structurally immune. Read this when a VC over secret data unexpectedly reduces
  to False, before branching on or comparing secret values, or when choosing between
  relop/bool and pure-`bv` forms for secret-dependent code (e.g. constant-time
  crypto). Framework-wide (theories/); assumes the `relval-model` value model; the
  `secLeakvar` contract permission itself lives in `cfgver-contracts`. A library skill.
---

# The secret-data observation walls

Secrets may freely *exist* as values (see **`relval-model`**: `NonSyncVal` is
contagious but never crashes). The model forbids *observing* them. Three sites turn
a `NonSyncVal` into `False` — this is the noninterference boundary. All in
`theories/Syntax/Formulas.v`:

| Site | On `NonSyncVal` | Meaning |
|------|-----------------|---------|
| `formula_bool t` (line 142) | `⇒ False` | can't take a branch / assume a path condition that depends on a secret |
| `formula_relop op t1 t2` (line 147) | `⇒ False` | can't assert a secret-dependent comparison |
| `secLeak rv` (line 117) | `SyncVal ⇒ True`, `NonSyncVal ⇒ False` | value declared public; a secret one is a leak |

`secLeakOtherDef` (Formulas.v:129): `secLeak rv ↔ rv = SyncVal (projLeft rv)`. In
CFGVer the `secLeakvar "v"` assertion is the *permission* that makes `"v"` public;
its **absence** is what makes a value secret (see **`cfgver-contracts`**).

## `term_eq` / `relop` on secrets — safe as a VALUE, fatal as a FORMULA

`term_eq = term_binop (bop.relop bop.eq)`, denoting `liftBinOp (eval_relop_val eq)`.
On a secret it yields a **`NonSyncVal bool`** — it does *not* crash. But that bool
is lethal the instant it is used as:

- a branch / path condition → `formula_bool` → `False`;
- a relational comparison formula → `formula_relop` → `False`;
- a publicness check → `secLeak` → `False`.

This is exactly right for **constant-time** code: CT idioms compute comparisons
*as bits* and feed them into arithmetic masks, never branching on them. So a
comparison-derived bit on secret data is fine *as long as it stays a value*.

## Practical rules for term-rewrite / peval / solver work on secret data

1. **Prefer pure-`bv` arithmetic canonical forms.** A form built only from
   `bvand/bvor/bvxor/shiftr/bvadd/bvsub/bvcons` never produces a `bool`, so it is
   *structurally immune* to the `NonSyncVal ⇒ False` trap. (This is why the
   mask-folding work chose all-`bv` forms and avoids `relop` entirely — see
   `CFGVer/PLAN-solver-fold.md`.)
2. **If you must introduce `relop`/`term_eq`** on data that can be secret, keep it a
   value sub-term (e.g. an argument to `bvcons`) and guarantee no rule ever lifts it
   into a `formula_bool` / `formula_relop` / `secLeak` position. On secret operands
   the whole point is that it stays symbolic and is never decided.
3. **Solver caveat:** the solver already special-cases `term_eq (term_val v) t` under
   a `SyncVal true` assumption (`Solver.v:1028`) — eq-terms have sync-context
   handling elsewhere, so a fresh value-level eq-term can be grabbed by rules that
   assume it is (or will become) synced. Another reason to stay in pure `bv` form.

> Note: this wall governs anything that becomes a *formula*. A rewrite whose two
> sides are both **pure terms** is a different regime — it is auto-sound over
> secrets with no case analysis (see **`relval-rewrite-over-secrets`**).
