# PLAN — forward world-GC ("unquantify more than once")

Successor to `PLAN-unquantify-gate.md`, which is now **complete and closed**.
That plan asked: *are there dead logic variables to drop?* Answer: yes, ~29 per
loop trip, and by the end of execution all but one of them are occurrence-dead
(`Example/ZZ-ARMS.md`, fifth arm). It also confirmed the thing it warned about —
a post-hoc prune is a 1% **slowdown** and leaves the scaling exponent exactly
where it was.

This plan asks the follow-on question: **can we drop them during execution, once
per instruction step, so that the world stays small and every subsequent
`persist`/`subst`/solver call is cheaper?**

---

## §0 What is already on disk

Branch `unquantify-gate`, commits `d301d482..bcecaaea`:

| commit | contents |
|---|---|
| `d301d482` | Phase A probe files |
| `c5437a16` | `theories/Symbolic/GenOccursCheck.v` ported from `main` + `Base.v` wiring + `SubstSU`/`GenOccursCheck` instances in `Formulas.v`, `Chunks.v`, `Messages.v`, `OccursCheck.v` |
| `929d55c6` | `Section Unquantify` in `Propositions.v`; `ty.inhabit` ported into `TypeDecl.v` |
| `bcecaaea` | `Example/ZZUnqCommon.v` + `ZZUnqRun*.v` measurement harness |

**All soundness proofs in that port are `Admitted`.** It was built to produce
node counts, and it is not on the trusted path of any example. Nothing in this
plan requires discharging them *unless* §4 Option B is taken — §3's design does
not use `unquantify` or `GenOccursCheck` at all. Keep that in mind before
budgeting time for `gen_occurs_check_laws_term`.

---

## §1 CORRECTION to the previous plan's difficulty assessment

`PLAN-unquantify-gate.md` §C.4 said forward GC would be "a refactor of the world
discipline, not a drop-in", on the belief that shrinking a world mid-execution
breaks the monad's monotone accessibility threading. **That belief is false and
should not be propagated.** Evidence, all pre-existing on this branch:

- `acc_subst_right {w} x {σ xIn} (t : Term (w - x∷σ) σ) : w ⊒ wsubst w x t`
  — `theories/Symbolic/Worlds.v:381`. The right-hand world's `wctx` is
  `ctx.remove xIn` (`Worlds.v:1825`). So `⊒` is **not** "context only grows";
  it is substitution-accessibility, and it shrinks.
- `acc_triangular : Tri w1 w2 -> w1 ⊒ w2` (`Worlds.v:428`) chains that over a
  whole triangular substitution, i.e. drops *many* variables at once.
- `SPureSpec.assume_pathcondition` (`theories/Symbolic/Monads.v:336-350`)
  already calls its continuation at a different, smaller world:
  `POST (wpathcondition w1 C1) (acc_triangular ν ∘ acc_pathcondition_right w1 C1) tt`.
  Its own comment calls this "the place where we really meaningfully change the
  world". This runs at **every** `assume`/`assert` in the executor already.
- The matching SymProp wrapper exists too:
  `assume_triangular {w1 w2} (ξ : Tri w1 w2) : 𝕊 w2 -> 𝕊 w1`
  (`theories/Symbolic/Propositions.v:311`), built from the `assume_vareq`
  constructor whose continuation is at `Σ - x∷σ`.

So the mechanism for "continue at a smaller world" is trusted, exercised on
every step, and already has refinement lemmas. What this plan adds is only a new
*reason* to invoke it (occurrence-death rather than solver-derived equality).

---

## §2 Phase 0 — measure the FORWARD-visible dead count (do this first)

**This is the gate. Do not write the combinator before this number exists.**

Phase B measured how many binders are dead *given the whole finished tree*. That
is not the number this plan can exploit. Mid-execution we cannot see the future;
a variable can only be dropped if it is absent from the state the continuation
can still read:

```
live(w) = fv(heap) ∪ fv(apc) ∪ fv(wco w) ∪ fv(tbl) ∪ fv(exits)
```

`fv(wco w)` is the dangerous one. A freshly-demonic `an` typically *does* occur
in the path condition (via the equality the fetch contract produces), so it is
forward-live even though `postprocess`+`unquantify` prove it globally dead. The
forward number could therefore be far below 29/trip — possibly zero. **We do not
know it yet, and the whole plan is worthless if it is small.**

### Phase 0 steps

1. New throwaway `Example/ZZFwdCommon.v` (mirror `ZZUnqCommon.v`'s style;
   `Require Export` the Prelude, stays out of `_CoqProject`).
2. Add a *purely additive, non-shrinking* instrumentation copy of the executor.
   Copy `sexec_cfg_addr` (`Verifier.v:275-292`) to `sexec_cfg_addr_probe` in the
   probe file, and at the recursion point emit a `SymProp.debug` node carrying
   the counts before recursing. Counting a variable as dead needs, for each
   `b ∈ wctx w`, an occurs check against heap/apc/wco/tbl/exits. Reuse the
   existing `OccursCheck` class (`theories/Symbolic/OccursCheck.v`) — the
   `occurs_check` for each of `SHeap`, `Term`, `PathCondition` already exists and
   returns `None` exactly when the variable occurs. Do **not** use
   `GenOccursCheck` here; `OccursCheck` is simpler and already instantiated for
   every type involved.
3. Record, per trip: `|wctx w|`, and how many of those are dead against
   (a) heap+apc+tbl+exits only, and (b) that **plus** `wco`. Report both — the
   gap between (a) and (b) is exactly the population that a smarter
   path-condition treatment (§5) could unlock.
4. Extend the `NC` record or add a parallel `FWD` record so the counts come out
   of one `vm_compute`, one `Eval` per `coqc` process (the harness rule in
   `ZZCommon.v`'s header — several heavy Evals in one process contaminate each
   other's timings and GC state). Run at N=1, 2, 4.

### Phase 0 gate

Let `d` be the mean per-trip count under criterion (b), against ~29 live
variables added per trip.

| `d` per trip | verdict |
|---|---|
| ≥ 20 | **GO** — proceed to §3 |
| 5–19 | **PARTIAL** — proceed, but expect a constant-factor win, not a change of exponent; re-read §6 before spending more |
| < 5 | **STOP** — report the (a)-vs-(b) gap and go to §5 instead; the binders are pinned by the path condition and dropping them is not the lever |

Phase 0 is a few hours and touches no trusted file. Report the number before
continuing, per the "decision checkpoints" rule in `CLAUDE.md`.

---

## §3 Phase 1 — the GC combinator (Option A: chained single-variable drops)

Assuming GO. The design needs **no new core machinery**.

To drop a dead `x∷σ` we substitute it by an arbitrary inhabitant rather than
removing it outright — that is what makes it an ordinary `acc_subst_right` step
instead of a new kind of accessibility. The witness comes from `ty.inhabit`
(`theories/Syntax/TypeDecl.v`, ported in `929d55c6`), which is exactly why
`main`'s `unquantify` needs it too.

```coq
(* in Monads.v, SPureSpec module, near assume_pathcondition *)
Definition gc_dead : ⊢ SPureSpec Unit :=
  fun w POST =>
    let ξ : Tri w _ := build_dead_tri w in   (* see below *)
    SymProp.assume_triangular ξ (POST _ (acc_triangular ξ) tt).
```

`build_dead_tri` walks `wctx w`, and for each `b∷σ` that is dead against
heap/apc/wco/tbl/exits **and** for which `ty.inhabit σ = Some v`, emits
`tri_cons b (term_val σ v)`. Everything else is `tri_id`. Note `ty.inhabit`
returns `None` for `tuple`/`union`/`record`, so those are simply never dropped —
a sound, silent under-approximation. `xlenbits` is `bvec`, which inhabits, so
`an` and `encoded_instr` are covered.

Two things to be careful about:

- **`gc_dead` must see the heap**, so the real combinator belongs at
  `SHeapSpec` level (`Monads.v:914`, `□(A -> SHeap -> 𝕊) -> SHeap -> 𝕊`), not
  `SPureSpec` — the pure layer cannot see the heap and would compute a wrong
  liveness set. Write it as a bespoke `SHeapSpec` definition, not via
  `lift_purespec`.
- **`tbl`/`exits` are extra roots** that no existing combinator knows about.
  They are arguments of `sexec_cfg_addr`, not part of the monadic state. Either
  pass them into the GC call as explicit extra roots, or (cleaner) have
  `sexec_cfg_addr` call GC itself and hand them in. The second is preferred and
  is why the call site is in `Verifier.v`, not buried in `Monads.v`.

### Call site

One line, at `Verifier.v:291`, in the `Some i` branch:

```coq
| Some i =>
    ⟨ θ1 ⟩ apc' <- sexec_instruction i apc ;;
    ⟨ θg ⟩ _    <- gc_dead_roots (persist_itable θ1 tbl) (persist_etable θ1 exits) apc' ;;
    sexec_cfg_addr n' (persist_itable (θ1 ∘ θg) tbl) (persist_etable (θ1 ∘ θg) exits)
                      (persist__term apc' θg)
```

Gate it behind a flag in `default_config` (or a `bool` parameter on
`sexec_cfg_addr`) so the old path stays byte-identical and A/B timing is one
recompile apart.

### Phase 1 measurement

Re-run the ZZ harness at N=1, 2, 4 with GC on and off. **The number that matters
is the N=1→N=4 growth ratio, not the absolute seconds.** Baseline is 16.0x. If
GC leaves the ratio ≥ 14x it has not addressed the wall regardless of what it
does to absolute time — say so plainly rather than reporting a percentage.

### The real performance risk, stated up front

`wsubst w x t` recomputes `subst (wco w) (sub_single xIn t)`. A `Tri` of length
`d` therefore performs `d` full traversals of the path condition per trip. With
`d ≈ 29` this could easily cost more than the shrink saves — **`gc_dead` making
things slower is a plausible outcome, not a bug.** Measure before optimising. If
it is slower but the growth ratio improves, go to §4.

---

## §4 Phase 2 — batching (Option B), only if §3 is slower but directionally right

Replace the `Tri` chain with a single many-variable thinning, so the path
condition is traversed once instead of `d` times. This is where the
`unquantify` port finally earns its keep: `GenOccursCheck.v` already defines
`WeakensTo` (`WkNil`/`WkSkipVar`/`WkKeepVar`) — a batched context thinning —
along with `transWk`, `meetWk`/`meetSU`, `wkRemove` and `weakenIn`.

Required new pieces:

1. `acc_weaken {w w'} (wk : WeakensTo (wctx w') (wctx w)) : w ⊒ w'`, with
   `sub_acc` the thinning substitution. Model it on `acc_subst_right`
   (`Worlds.v:381`) and its `sub_acc` computation.
2. A SymProp wrapper analogous to `assume_triangular` that closes over all
   dropped binders at once. `main`'s `uq_demonicv` is the template.
3. `meetSU` to combine the minimal contexts of heap, apc, wco, tbl and exits
   into one target context in a single pass.

This is where the `Admitted` soundness lemmas in `c5437a16` become real work,
including `gen_occurs_check_laws_term` (Admitted because our extra
`term_relval` constructor shifts `main`'s fixed bullet script — it needs a fresh
script, not a port). Budget accordingly; do not start §4 without a §3 number
justifying it.

---

## §5 Fallback — if Phase 0 says the path condition pins everything

If the (a)-vs-(b) gap in §2 is large, the binders are alive only because `wco`
mentions them, and the lever is not occurrence-death but **eliminating the
defining equations**. `postprocess`'s `solve_uvars` already does this for
`assume_vareq`-defined variables but not for `assert_vareq`-defined ones, which
is the documented reason `an` survives postprocess
(`project-key-schedule-loop-scaling` memory note). Running that elimination
*forward*, per step, is then the alternative intervention — same call site, same
accessibility machinery, different liveness criterion. Scope it as its own plan
rather than bolting it onto this one.

---

## §6 Honesty clauses (carried over, still binding)

- **Do not report a speedup that is not a change in the growth ratio.** The
  measured wall is superlinear; a flat percentage off the top is not a fix and
  should not be described as one.
- **Do not quote wall-clock deltas below ~15%** on this box without back-to-back
  or user-CPU measurements. `ZZCommon.v`'s header documents the same computation
  measuring 0.68–1.13 s at N=1 and 15.9–20.8 s at N=4 across runs.
- **One heavy `Eval` per `coqc` process.** Non-negotiable; several in one process
  contaminate each other's GC state.
- The `unquantify` port is `Admitted` throughout. Any claim that a VC "verifies"
  on this branch must state that. Nothing here may be merged toward
  `bearssl-breaking-bad` while that is true.
- If §3 lands and works, the trusted-surface consequence is that
  `sexec_cfg_addr` changed, so `rexec_cfg_addr` and its `RefineCompat`
  instances in `VerifierRel.v` must be re-proved (see the `cfgver-refinement`
  and `cfgver-rsolve` skills). That is the real cost of this plan and it is paid
  in Phase 3, which is deliberately not scoped here — scope it once §3 has a
  number.
