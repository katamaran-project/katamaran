# PLAN — drop dead logical variables during symbolic execution

Status: **ABANDONED AT PHASE 0, 2026-08-25, the same day it was opened.** The
kill-gate fired: the local refinement lemma is **false**, for a reason readable
straight off `assuming`'s definition. Nothing was built. Fall back to the
wide-binder packing (`diagnostics/havoc-abstraction-payoff.md` §8.5, slope
1/trip) or go to a real loop rule (`PLAN-loop-invariant.md`, slope 0) — see
§"Phase 0 result" below for why the loop rule is the principled version of this
idea rather than a different one.

**The gate did its job.** It cost an afternoon of reading instead of a week of
building, and the design section below is kept exactly as pitched so the error is
legible. Read the Phase 0 result BEFORE believing any of it.

## The problem

The `havoc_regs` abstraction lemma (`PLAN-annotinstr.md` Phase 4) removes a
loop's per-trip TERM recurrence and pays for it in surviving LOGICAL VARIABLES:
one per havoced register per trip, because a demonically produced unconstrained
value is determined by nothing and so the solver can never eliminate it. Live
`|Σ| = 15 + kn` for k havoced registers, and declared-variable count is
quadratic in lookup cost (`diagnostics/lvar-lookup-cost-drivers.md`).

Measured (`diagnostics/havoc-abstraction-payoff.md` §8): cutting k from 7 to 3
is 2.66× at n=16 and is what makes br_divrem's real 31 trips reachable at all.
But it is a FACTOR — the local exponent is still 1.269 → 1.631 → 2.015 and
rising. Taking the slope to **zero** is what would make it an exponent fix.

Each trip's `hv` binders are dead the moment the next trip's havoc consumes
their chunk. They survive only because `demonicv_prune` (`Propositions.v:1175`)
collapses on `block` and nothing else.

## The idea, and the one thing that makes it sound

Drop a dead binder mid-execution: move to `wsubst w x t` and continue there.

**A previous verdict that this is UNSOUND is WITHDRAWN** (see
`diagnostics/havoc-abstraction-payoff.md` §8.1 for the full retraction). The
argument that killed it was that the deadness side condition is about the
continuation, which is a function. That is wrong: the condition is about the
PRESENT STATE. Every term the continuation can build is built from terms that
exist now, so a variable occurring nowhere now can never reappear.

What survives from that argument is the *mechanism*, and it is what the proof
has to get past:

- `acc_subst_right` (`Worlds.v:381`) is the ONLY accessibility into a smaller
  context (every `acc_*` in `Worlds.v:320-411` enumerated) and it needs a
  witness term.
- The only two embeddings from `SymProp (w-x)` back to `SymProp w` are
  `assume_vareq` and `assert_vareq` (`Propositions.v:281,314`).
- `safe` (`Propositions.v:340,345`): `safe (demonicv x k) ι = ∀v, safe k`,
  whereas the drop yields `safe k[x:=t]` — weaker unless x is absent from k.
  `assert_vareq` instead sends the VC to `False`.

**Why the refinement obligation is nevertheless dischargeable.**
`RHeapSpec RA := □ᵣ(RA -> RHeap -> ℙ) -> RHeap -> ℙ`
(`Refinement/Monads.v:1525`). A world-moving action instantiates the box with
`refine_four` (`refine_chunk_gc` uses `refine_T` only because `chunk_gc` sits at
`acc_refl`), which delivers the continuation relation under `assuming θ` — and
at a valuation ι with ι(x) ≠ `inst t` that `assuming` is vacuous. The way past
it is that **the concrete side carries no valuation**: `Φc : CA -> CHeap -> Prop`
is a plain Coq function, and the goal's only ι-dependence is the heap relation
`inst h ι = ch`. So

1. set ι₀ := ι[x ↦ `inst t (ι∖x)`];
2. `inst h ι₀ = inst h ι` — requires **x ∉ h**;
3. ι₀ ⊨ `wco w` — requires **x ∉ wco w**;
4. at ι₀ the equation holds, so `knowing_acc_subst_right`
   (`UnifLogic.v:1213`, already proved) turns `assuming` into `knowing` and
   hands over the continuation relation.

So the side condition is two `occurs_check`s on data and **nothing about `sΦ`**.
That is sound for the reason the whole idea rests on: the only channels by which
x could reach the continuation are the heap, the path condition, and solver
substitutions — and a solver substitution needs an equation, which lives in
`wco`. Both channels are checked.

**The check already exists with the right law.** `occurs_check`
(`Symbolic/OccursCheck.v:56`, in scope everywhere via `Base.v:68`'s mixin)
returns `Some` exactly when the variable does not occur;
`occurs_check_sound : occurs_check xIn u = Some u' → u = subst u' (sub_shift xIn)`
is precisely "does not occur ⟹ is a weakening". Instances cover Term, Formula
(`Formulas.v:301`), Chunk (`Chunks.v:188`), list, Env, pair, option and
Assertion (`Assertions.v:135`), so `SHeap = list Chunk` and
`PathCondition = list Formula` come free. `Symbolic/Monads.v:97-99,130-133`
already occurs-checks a (pathcondition, heap) pair. The unifier uses the same
check for the same purpose. Note `UnifLogic.v:1345` holds a commented-out
`assuming_acc_subst_right_left` — someone started on this corner and stopped.

## Design decisions

1. **A step of `sexec_cfg_addr`, NOT an `sexec_ghost` case.** Keep `Annot` as
   the trigger (`AnnotDropDead`) but have `sexec_cfg_addr` partition the ghost
   list and handle that constructor inline, where `tbl`/`exits`/`apc` are in
   scope. An `sexec_ghost` case cannot see them, which is the entire reason the
   original sketch did not work.
2. **Also `occurs_check` `tbl`/`exits`/`apc`** — not for soundness but for
   CORRECTNESS: transporting them substitutes `t` for `x` and would silently
   rewrite the instruction table. They never mention havoc variables, so this
   always passes; it must still be checked.
3. **Scan all of Σ, at the annotation point only.** |Σ| is 15–127 and the drop
   fires once per trip, so a full scan is affordable and collects any other dead
   binder for free. Firing every step would cost O(H·|Σ|) per step and could be
   a net loss.
4. **Witness term restricted to `ty.bvec`** (`term_val _ bv.zero`). There is no
   `Inhabited`/`defaultVal` class in the tree, so a general witness is not
   available — and every havoc variable is `ty_xlenbits`. A deliberate
   restriction, not a gap.
5. **`None` ⇒ no-op, never `error`.** A refused drop must cost completeness
   nothing: it is a missed optimisation, not a failure.

## Phases

**Phase 0 — KILL-GATE (~half a day).** Prove the refinement lemma for the
narrowing step, standalone, in a probe. Nothing else is built until it closes.
`VerifierRel.v` cannot be opened by pet at any position, so use the
restate-in-a-probe pattern; and since the definitions live inside module
functors, preamble mode cannot reach them — use position mode
`rocq_start(file=…, line=…)`, which replays through the project's real load
path. **Exit criterion:** the `Some` branch closes with only the two
`occurs_check` hypotheses. **If it needs `x ∉ sΦ` as well, STOP** and fall back
to the packing (slope 1/trip instead of 0).

**Phase 1 — symbolic side.** `AnnotDropDead`; the inline case in
`sexec_cfg_addr`; the candidate scan; k successive narrowings. **Instrument how
many drops actually FIRE** — a drop that never fires is indistinguishable from
one that works, and §8's positive controls show havoced values reaching
formulas (A5, A3) which would correctly refuse.

**Phase 2 — mirror and absorb.** Concrete side `pure tt`; re-pair
`rexec_cfg_addr`; absorb the new bind in `sound_exec_cfg_addr_myWP2`.
Known-shape work: the chunk-GC did exactly this, and Phase 4 did it for
`call_lemma`.

**Phase 3 — measure, then gate.** Same rig, protocol and baseline as §8:
`ZZAllocR3_*` (control, already measured) against R3+drop at n =
1,2,3,4,8,16,31. Read live |Σ| with §5c's fuel-starvation instrument, with the
matched baseline arm this time.

## Pre-registered success criterion

|Σ| flat at 15 instead of 15+3n, **and** the 8→16 local exponent materially
below R3's 1.631. **If |Σ| goes flat and the exponent does not move, STOP** —
|Σ| was not the residual driver, the remaining mechanism is unidentified, and
the packing must not be built on top. That is the `select_last_k` lesson: a
correct diagnosis and a working fix bought 12% because a different driver
dominated.

## Risks, in order

1. Phase 0 fails → fall back to packing. Cheap to discover, hence first.
2. **The drop never fires on the real program.** A havoced value that reaches a
   formula lands in `wco` and the check correctly refuses; §8's positive
   controls show exactly that for A5 and A3. A0/A1/A4 should be clean, but it is
   an empirical question — hence Phase 1's instrumentation.
3. Extra `assume_vareq` nodes per trip. Expected to be dominated by a flat |Σ|,
   but `Qed` needs its own look, since `Qed` re-runs the executor via the VM
   cast (so `Qed ≈ vm_compute`).

## Phase 0 result — THE GATE FIRED, and why

**The lemma is false.** `assuming` (`Worlds.v:755`) is

```coq
assuming ω P ι = forall ιpast, inst (sub_acc ω) ιpast = ι ->
                               instprop (wco w1) ιpast -> P ιpast
```

For `ω = acc_subst_right t` we have `sub_acc ω = sub_single xIn t`, so
`inst (sub_single xIn t) ιpast` is `ιpast` with `inst t ιpast` inserted at x, and
the premise `= ι` forces **`ι(x) = inst t (ι∖x)`**. But the premise of the whole
enterprise is that x is UNCONSTRAINED — absent from `wco w`, which is exactly
what makes it droppable. So at the generic ι no `ιpast` exists, the hypothesis
`assuming ω (psafe K)` is **vacuously true**, and the goal `⌜Φc tt ch⌝` still has
to be produced. Nothing else in the context can produce it. Hence
`⊢ ℛ⟦RHeapSpec RUnit⟧ (pure tt) (drop_var …)` does not hold.

**Where the pitch above went wrong.** Its step 1–4 argued: the goal is
x-independent (true — `Φc` carries no valuation and `x ∉ h`), so evaluate at
ι₀ := ι[x ↦ inst t] where the equation holds and `knowing_acc_subst_right`
applies. The flaw is that `⊢` in `Pred` is **pointwise in ι**: we are handed the
hypothesis at ι and must discharge the goal at ι. Being able to prove the goal at
some *other* valuation is not available as a step. x-independence of the goal is
true and useless.

**What is actually true, and it is the reusable part.** The fact that rescues the
drop is that the enclosing binder universally quantifies x — and that fact lives
OUTSIDE the action. `psafe (demonicv x k) = assuming acc_snoc_right (psafe k)`
(`Propositions.v:2431`), the drop is `assuming (acc_subst_right t) …`
(`:2439`), and `assuming_trans` (`UnifLogic.v:961`) composes them. Mint
immediately followed by drop collapses: the composite accessibility
`w ⊒ wsnoc w x ⊒ wsubst (wsnoc w x) x t` lands back at `w`, and
`assuming acc_refl P ⊣⊢ P` (`:939`). **So soundness is a property of the
MINT/DROP PAIR, not of the drop.** A real theorem here has to quantify over
everything the executor emits between the two — every intervening world
extension must itself be x-free for the composite to collapse. That is a
substantially larger obligation than the one pitched, and it is about a subtree
rather than a step.

**Consequently the principled version of this idea is a loop rule, not an
annotation.** A loop invariant closes the binder AT the loop head, which makes
the mint/drop pairing lexically explicit; the drop tries to shrink a lexical
scope from the inside, which is why it needs a non-local justification and the
loop rule does not. `PLAN-loop-invariant.md` is therefore not an alternative to
this plan — it is this plan done in the place where the framework can express it.

**Two `occurs_check` facts remain correct and worth keeping**, since a future
attempt needs them either way: `occurs_check`
(`Symbolic/OccursCheck.v:56`, in scope via `Base.v:68`) with
`occurs_check_sound : occurs_check xIn u = Some u' → u = subst u' (sub_shift xIn)`
decides deadness on data, and `Symbolic/Monads.v:97-99` already runs it on a
(pathcondition, heap) pair. The semantic claim behind the whole plan — a variable
occurring nowhere in the present state can never reappear, because every future
term is built from present terms — is **also correct**. Neither fact is what
blocks it.

## Log

**2026-08-25 — plan opened, Phase 0 run, plan abandoned.** Author's note, since
the flip-flop is the expensive part: I first called the drop UNSOUND (wrong —
retracted in `diagnostics` §8.1), then called it locally provable and pitched
this plan (also wrong — it fails on `assuming`'s vacuity). The check that
settled it, reading the definition of `assuming`, cost about two minutes and
should have come BEFORE the pitch, not after. The semantic intuition that
started it was right throughout; what neither verdict engaged with until now is
the framework's pointwise-in-ι entailment.
