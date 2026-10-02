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

> **CORRECTED 2026-09-30.** This skill used to say `RelVal` equality is
> "exactly both projections equal", so that every `Val` identity lifts.
> **That is false.** The ring-normalisation port (`PartialEvaluation.v`,
> `PLAN-bv-arith-solver.md` U3) ran into it: `x - x ~> 0` is a true `bv`
> identity, but an UNSOUND rewrite when `x` is secret. (The description above
> still states the old claim; fixing it needs a `skill-routing-maintenance`
> consult.)

**Bottom line:** a Term rewrite proved as a `Val`/`bv` identity is sound over
all `RelVal` inputs, secrets included, **provided both sides mention the same
set of leaves** (term variables and `term_relval` constants). Under that
condition you never case-split `SyncVal` vs `NonSyncVal`. Without it, the
rewrite can make a secret look public.

## Why

`RelVal = RV (Val σ)` has two constructors, and `SyncVal v <> NonSyncVal v v`.
Every lifted op (`liftBinOp`/`liftUnOp`, `TypeDecl.v:374`, see
**`relval-model`**) returns `SyncVal` iff **all** its operands are `SyncVal`.
So `inst t ι` carries two pieces of information:

1. **its two projections.** These are homomorphic
   (`comProjLeftLiftBinOp`/`comProjRightLiftBinOp`, `TypeDecl.v:385`), so a
   `Val` identity makes them agree on both sides;
2. **its SyncVal-ness.** `inst t ι` is `SyncVal` iff every leaf of `t` is
   `SyncVal` under `ι`. A `Val` identity says nothing about this.

Point 2 is observable: `secLeak` is `False` on every `NonSyncVal`, so
`NonSyncVal 0 0` (`x - x`, `x` secret) and `SyncVal 0` (the literal `0`) can be
told apart. Two terms are equal as `RelVal`s iff both points hold, and the
same-leaves condition supplies point 2.

## In practice

- **Rules that keep every operand** (associativity, commutativity, folding
  literal constants, the mask-algebra rules) have the same leaves on both
  sides. Prove the `bv` fact and lift it, with no RelVal case split. Example:
  `peval_bvadd_sound`.
- **Rules that can DROP an operand** (cancellation `x - x`, `0 * x`, `x & 0`,
  ring normalisation in general) must either keep the dropped atom or fire only
  when the dropped operand is a literal. The ring normaliser keeps it: `pad`
  re-adds it as `0 * x`, and `same_leaves` checks the result, both in
  `PartialEvaluation.v`.
- **Proof pattern for the general case:** first prove equality on each
  projection. This is `teq side`, and the ring axioms hold there. Then show the
  SyncVal-ness agrees, using the computable leaf-set check (`teq_leaves_inst`).

## The one caveat

This covers rewrites where **both sides are pure terms**. The moment a rewrite
produces (or depends on) a *bool that gets used as a formula / branch / secLeak*,
the pure-term argument no longer applies — a `NonSyncVal` bool is `False` in those
positions. That regime, and why it pushes secret-dependent canonical forms toward
pure-`bv` arithmetic, is **`secret-data-walls`**.
