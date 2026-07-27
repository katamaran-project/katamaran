---
name: cfgver-rsolve
description: >
  Using Katamaran's rsolve tactic effectively — the relational automation that closes
  symbolic-vs-concrete goals via RefineCompat instance search. Use when rsolve fails,
  hangs, seems stuck in a Qed, or eats multi-GB memory (rocq-mcp pet dying with
  memory_exhausted); when a RefineCompat instance is missing and must be written; or
  when binds must be paired manually with HeapSpec.refine_bind. Covers the
  Set Typeclasses Debug workflow, the #[export] Instance template, the divergence
  failure mode, and the PureSpec name-shadowing trap. NOT for what the relation or
  the concrete mirror IS (cfgver-refinement).
---

# Driving `rsolve` effectively

`rsolve` closes relational (ℛ⟦⟧) goals by typeclass search over `RefineCompat`
instances (→ **cfgver-refinement** for the relation itself). It is powerful but
fails non-gracefully; this skill is the craft of using it.

## When `rsolve` fails: the debugging workflow

1. `Set Typeclasses Debug.` and rerun `rsolve`.
2. Read the search trace for the goal pairing that found no instance.
3. Write the missing instance (template below) or, if the heads genuinely differ,
   pair manually (next section).

## Adding a `RefineCompat` instance

```coq
#[export] Instance refine_compat_my_thing {Σ : LCtx} (params...) {w} :
    RefineCompat (LogicalSoundness.RProp)
      (cconcrete_thing params) w (ssymbolic_thing params w) _ :=
    MkRefineCompat (rmy_thing params).
```

where `rmy_thing` is the relational-correctness lemma proved separately. The
`#[export]` matters — without it the instance is invisible outside the section.

## Divergence / `memory_exhausted`

If `rsolve` eats multi-GB RAM or the rocq-mcp pet dies: it reached a goal pairing
heads with **no matching instance** (e.g. `cexec_cfg_addr` vs `sexec_cfg_addr`,
or two monadic programs whose bind structures are misaligned) and the search
diverged instead of failing. It can also present as an apparent `Qed` hang.

Fix: pair the binds manually —

```coq
iApply (HeapSpec.refine_bind (RA := ...)).
```

— and run `rsolve` only on the aligned atomic subgoals. Dispatch the table executor
with `rexec_cfg_addr` rather than hoping search aligns it.

## Name-shadowing trap

`Import PureSpec.` (VerifierRel.v, Relational section) shadows the HeapSpec names for
everything below it: a bare `refine_bind` resolves to the **PureSpec** variant and
`iApply` fails on a CHeapSpec/SHeapSpec goal. Qualify: `HeapSpec.refine_bind`.
