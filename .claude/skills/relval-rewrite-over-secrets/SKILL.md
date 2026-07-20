---
name: relval-rewrite-over-secrets
description: >
  Why a peval / solver / Term-level rewrite proved as a plain bv/Val identity is
  AUTOMATICALLY sound relationally — including on secret (NonSyncVal) inputs — with
  NO separate SyncVal/NonSyncVal case analysis. Because `inst` and the lifting
  operators are homomorphic, term equivalence `≡` reduces to componentwise Val
  equality on projLeft/projRight, so a pure `Val` identity lifts to both SyncVal and
  NonSyncVal for free. Read this BEFORE adding or proving a `peval` case, a solver
  rule, or any Term rewrite that could touch private data, or whenever unsure
  whether a rewrite must handle NonSyncVal specially (for pure terms: it does not).
  Framework-wide (theories/) library skill; assumes the `relval-model` value model.
  Caveat: only holds when BOTH sides are pure terms — a bool that reaches a
  formula/branch is governed by `secret-data-walls`, not this skill.
---

# Rewrite soundness over secrets

**Bottom line:** a Term-rewrite rule proved as an ordinary `Val`/`bv` identity
(`∀ concrete args, lhs = rhs`) is sound relationally over *all* `RelVal` inputs,
including `NonSyncVal`. You never case-split `SyncVal` vs `NonSyncVal` for a
pure-term rewrite.

## Why (the homomorphism argument)

Term equivalence `t1 ≡ t2` means `∀ ι, inst t1 ι = inst t2 ι` as `RelVal`s, and
`RelVal` equality is exactly *both projections equal*. Because `inst` and the
lifting operators (`liftUnOpRV`/`liftBinOpRV`, see **`relval-model`**) are
homomorphic — `projLeft (liftBinOp f a b) = f (projLeft a) (projLeft b)`
(TypeDecl.v:372), and the `projRight` twin — this reduces to:

> the underlying **Val-level functions agree on `projLeft` and on `projRight`**.

So proving the plain Val/bv identity discharges the relational obligation on every
input shape at once. A `SyncVal` is just the case where both projections coincide;
a `NonSyncVal` applies the same identity independently to each side.

## In practice

This is why the existing peval simplifiers are discharged by peeling to a `bv`
fact: e.g. `peval_bvadd_sound` (PartialEvaluation.v:839) proves
`peval_bvadd t1 t2 ≡ term_binop bop.bvadd t1 t2` via `intros ι; cbn; …` down to a
`bv.add` associativity/commutativity fact — no `RelVal` case analysis appears.

When you add a new pure-term rewrite (a `peval_*` case, a fold rule, a
normalizer step): state and prove it as a `Val`/`bv` equation, then lift with the
homomorphism lemmas. Secrets require no extra work.

## The one caveat

This covers rewrites where **both sides are pure terms**. The moment a rewrite
produces (or depends on) a *bool that gets used as a formula / branch / secLeak*,
the pure-term argument no longer applies — a `NonSyncVal` bool is `False` in those
positions. That regime, and why it pushes secret-dependent canonical forms toward
pure-`bv` arithmetic, is **`secret-data-walls`**.
