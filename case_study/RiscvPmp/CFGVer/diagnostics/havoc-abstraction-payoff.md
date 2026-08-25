# br_divrem: a register-havoc ghost lemma removes the per-trip term recurrence

**Finding.** Invoking a `havoc_regs` abstraction lemma on br_divrem's loop head —
consuming the seven loop-carried registers' points-to and producing fresh
existentials — removes the multiplicative per-trip cost entirely: **plain costs
≈10× more per additional trip (7.71×, 9.97× over n=1→2→3), the havoc arm's
successive doublings cost 2.29×/3.04×/4.08×**. At n=3 that is **32.9×** less
allocation; n=16 with the havoc costs 28.9 G words, which plain would not reach
by roughly thirteen orders of magnitude. **This is an exponent change, not a
constant factor** — the thing `PLAN-annotinstr.md` Phase 4 predicted and the
first measured evidence for it.

Two things it is *not*. It is not "λ → 1": what remains grows polynomially with a
**rising** local exponent (1.19 → 1.60 → 2.03 over successive doublings), and a
quadratic fit on n=2,4,8 under-predicts n=16 by 13%, so **no growth law is
established here — do not quote one.** And it is not free: the lemma leaves **7 fresh logic
variables per trip alive in the world** (`|Σ| = 15 + 7n`, against a flat 15
without it — §5c), because a demonically produced unconstrained value is not
determined by anything and so cannot be solved away, unlike all 659 of the
executor's own per-trip mints. Those binders are dead as soon as the next trip
havocs the register again, which makes them the named target for the
drop-an-unreferenced-variable annotation.

## 1. The axes

| axis | states | what moves it |
|---|---|---|
| `ghost-machinery` | absent / present-but-empty | arm A vs arm B — same `call_lemma`, empty register list |
| `havoc-target` | none / dead-temps-only / all-loop-carried | arms B, C, D |
| `trip-count` | n = 1,2,3,4,8,16 | the `li A5, n+1` immediate; program LENGTH is constant in n |

Arm B exists because a ghost that fires once per trip changes the tree by
itself, and four harnesses in this project have been vacuous for want of a
control. Arm C exists because the six growing slots measured in
`PLAN-annotinstr.md`'s 2026-08-24 entry (x5 x6 x10 x11 x14 x28) include four
temporaries that are *dead at the loop head* — each is written at index 9/10/14/24
before any read in the trip — so havocing them alone is information-lossless and
was the a-priori "free win" candidate. It is not one; see §5.

| arm | ghost planted on the loop head (index 8) | registers havoced |
|---|---|---|
| A | none | — |
| B | `AnnotLemmaInvocation (havoc_regs [])` | none |
| C | `AnnotLemmaInvocation (havoc_regs zz_temps)` | T0 T1 T2 T3 |
| D | `AnnotLemmaInvocation (havoc_regs zz_all)` | T0 T1 T2 T3 A0 A1 A4 |

**Never havoced, deliberately:** A5/A6/A7 (the loop counters the back edge is
decided on — they must stay concrete), A2 (read-only divisor), A3 (base pointer).

## 2. Protocol

Every row below shares one protocol; a figure recorded without it is not a
measurement.

- **Metric** `allocated_words` (`OCAMLRUNPARAM='v=0x400'`), **net of a baseline**
  of 611,564,884 words (`ZZAllocF_BASE.v` — identical definitions, no `Eval`).
- **Tree only, no VC proof.** `Eval vm_compute in (top_kind t, measure t)` over
  `postprocess (CFG_VC_triple …)`. `solve_vc` never runs, so
  `ZZDivremProbe2.v`'s unresolved `solve_symbase_fetch` residual is irrelevant.
- **One `Eval` per `coqc` process.**
- **Fuel `27n + 60` in every arm** — NOT the rig's own `26n + 40`; see §4.
- Rig copied verbatim from `ZZDivremNCommon.v`: 12 registers, one memory cell,
  both fixed in n, so the chunk inventory cannot grow and anything moving here
  is term size or variable count.

## 3. Results

Net allocated words, in units of 10⁹.

| n | A plain | B `havoc []` | C havoc temps | D havoc all seven |
|---|---|---|---|---|
| 1 | 0.6858 | 0.6859 | — | 0.5684 |
| 2 | 5.2852 | — | — | 1.0183 |
| 3 | 52.6759 | 52.6777 | 102.2676 | 1.5997 |
| 4 | — | — | — | 2.3299 |
| 8 | — | — | — | 7.0787 |
| 16 | — | — | — | 28.9014 |

Every cell above is `("BLOCK-vc-discharged", (1,0,0))` — the VC is *discharged*,
checked explicitly, because `count_nodes = 1` holds for `SymProp.error` just as
it does for `SymProp.block` and a fast arm that had merely *failed* would be
indistinguishable otherwise.

**Growth.** Plain is multiplicative per trip: 0.6858 → 5.2852 → 52.6759 is
**7.706× then 9.967×**, independently reproducing the λ ≈ 10.1–10.5 steady state
that `PLAN-annotinstr.md` measured by a completely different route (printed heap
chars and `term_` node counts).

Arm D per doubling: 1.0183 → 2.3299 → 7.0787 → 28.9014, i.e. **2.288× / 3.038× /
4.083×**, local exponents 1.194 / 1.603 / 2.030.

**Held-out fit (required, and it FAILS).** A quadratic fitted on n = 2, 4, 8
predicts n=16 at 25.08 G against 28.90 G actual — **−13.2%**. A power law fitted
on n = 4, 8 predicts 21.5 G — **−25.6%**. So arm D is superquadratic in the
measured range and its exponent is still rising. **Not established as quadratic;
quote the doubling ratios, not a law.**

## 4. The completeness edge that wasn't — RETRACTED before publication

An earlier pass of this experiment (fuel `26n + 40`, the rig's own formula)
found arm D discharging to `block` up to n=16 and leaving a residual from n=18
on — 144 nodes / 141 binders at n=18, 158/155 at n=20, 172/169 at n=22, 186/183
at n=24 — and that was written up as a completeness limit of the havoc.

**It is fuel exhaustion in the rig, and has nothing to do with the havoc.** The
loop body is indices 8..34 = **27** instructions per trip, so the real
requirement is `8 + 27n + 15 = 27n + 23`, which overtakes `26n + 40` at exactly
n = 18. Re-run at `27n + 60`, n = 16, 18 and 20 all discharge to
`BLOCK-vc-discharged`. The plain arm could never reach n=18, which is why the
rig's off-by-one-per-trip fuel had gone unnoticed.

The residuals were still worth having: `binders = 15 + 7n` exactly, at every
failing n, which is how `|Σ|` growth is known to be **one fresh variable per
havoced register per trip** rather than inferred.

*Method note, since the near-miss was cheap only by luck:* the tell was that the
failure appeared at a trip count no other arm could reach. A threshold that only
one arm is fast enough to observe is a property of the *rig* until proven
otherwise.

## 5. Reading the axes apart

**`ghost-machinery` — free.** Arm B against arm A at the same n: **1.000081×** at
n=1 and **1.000035×** at n=3. Planting a `call_lemma` on the loop head and
consuming/producing `⊤` costs four thousandths of a percent. So nothing in §3's
D column is attributable to the annotation existing.

**`havoc-target: dead temps` — actively harmful, 1.941×.** Arm C at n=3 costs
102.27 G against plain's 52.68 G. Havocing four registers that are provably dead
at the annotation point, losing no information whatever, **nearly doubles the
cost.** The consume/produce is not free and buys nothing, because the temps'
term size is a *symptom*: they are recomputed from A0/A1/A4 every trip, so
resetting them leaves the recurrence that generates them untouched and they grow
straight back within the same trip.

This is the useful negative result in the study. "Which slots are large" and
"which slots carry the recurrence" are different questions, and the six-slot
measurement in `PLAN-annotinstr.md` answers only the first. **An abstraction
lemma must target the loop-carried values, not the largest terms.**

**`havoc-target: all loop-carried` — the whole effect.** D against A at the same
n: 0.829× at n=1, **5.19×** at n=2, **32.9×** at n=3. The ratio grows without
bound because the two arms have different growth *shapes*, which is exactly why
a single-N speedup figure would be meaningless here.

## 5b. Direct measurement: term growth and variable count (2026-08-25)

§3–5 measure aggregate allocation, which is indirect evidence for a claim about
*term size*, and §4's `|Σ| = 15 + 7n` came from FUEL-STARVED runs. Both are now
measured directly, in the healthy configuration.

**Method.** An `AnnotDebugBreak` on the loop head is what makes either readable:
without one the postprocessed tree collapses to `block` (`demonicv_prune` folds
a binder spine over `block`), so there is no heap to dump and no binder to count.
Arm **E** plants `[break; havoc; break]`, and since `ai_ghost_before` runs in list
order that gives the PRE- and POST-havoc heap at the same pc on the same trip —
one run, no cross-run comparison to get wrong. Sizes are printed characters of
each register's term at `Set Printing Width 1000`.

### Term size in the loop-carried registers, at the loop head

| trip | baseline (break only) | havoc: PRE | havoc: POST |
|---|---|---|---|
| 1 | 243 | 243 | 117 |
| 2 | 8,244 | 5,203 | 123 |
| 3 | 88,468 | 5,256 | 126 |

(Whole-heap chars: baseline 814 / 8,815 / 89,039. That independently reproduces
the 786 / 8,787 / 89,011 measured 2026-08-24 by a different session, and pins
the baseline's steady-state λ at **10.7**.)

**The recurrence is broken, and the dump shows the mechanism outright.**
Post-havoc every watched register holds a bare `term_var "hv.N"` (15–18 chars).
The PRE-havoc term at trip 2 is built out of `hv.4`/`hv.5` — *last trip's* fresh
variables — so each trip constructs one trip's worth of nesting and is reset,
instead of nesting on top of the previous trip's term. That is why PRE is flat
after the first trip (5,203 → 5,256, +1.0%) rather than growing ×10.7.

At trip 3 the comparison is 88,468 against 5,256 — **16.8×** at the worst point
inside the trip — and that ratio grows by roughly the baseline's λ per further
trip.

### Variables spawned

Counted on the **RAW** tree (`CFG_VC_triple` with no `postprocess`), summing
every binder node anywhere rather than the leading spine — `count_binders` walks
only the leading spine and reads 4 on a raw tree regardless, which is a trap
worth knowing before quoting it.

| | demonicv | angelicv | per trip |
|---|---|---|---|
| no havoc | 493 / 758 / 1023 | 708 / 1102 / 1496 | +265 / +394 |
| havoc | 500 / 772 / 1044 | 715 / 1116 / 1517 | +272 / +401 |
| **difference** | **+7 / +14 / +21** | **+7 / +14 / +21** | **+7 / +7** |

So the havoc mints **exactly 7 demonic + 7 angelic variables per trip** — one
each per havoced register, the angelic one being the instantiation that consumes
`∃v, r ↦ v` — against a baseline of 659 mints per trip. That is **+2.1%**.
It also adds exactly 21 raw nodes per trip.

**Surviving `postprocess`: zero, in both arms** (tree is `block`, 1 node, 0
binders, at every n). But that is a fact about the FINAL TREE, not about the
live world — see §5c, which measures the live world and reaches the opposite
conclusion about cost.

### 5c. Live world size — `|Σ| = 15 + 7n` STANDS (and a retraction of a retraction)

*History, because the reasoning is the reusable part.* §4 read `binders = 15 + 7n`
off the fuel-starved n≥18 residuals. An earlier version of this section then
RETRACTED that, on the grounds that fuel starvation is a broken configuration and
that healthy runs read 15 flat. **That retraction was itself wrong and is
withdrawn.** Starvation is not a confound here, it is the INSTRUMENT: a healthy
run's tree collapses to `block`, `demonicv_prune` folds the whole binder spine
away, and `DebugAsn` has no variable-context field to snapshot `Σ` with — so
there is no other way to read the live world back out. What makes the instrument
trustworthy is the control that was missing the first time round.

**The control.** Same starvation, both arms, n = 1,2,3:

| arm | binders | distinct `hv` names |
|---|---|---|
| no havoc | 15 / 15 / 15 | 0 / 0 / 0 |
| havoc | 22 / 29 / 36 | 7 / 14 / 21 |

The baseline is **flat at 15 under identical starvation**, so the 7-per-trip is
the havoc's and not an artifact of starving. And the names settle their origin
without inference — the extra binders are literally `hv`, `hv.1`, … `hv.20`,
against the baseline's fixed `p, w, np, v, v.1…v.10, mv`. Twenty-one distinct
names at n=3, none reused.

**So `|Σ| = 15 + 7n` in the live world, and it is a real asymmetry, not a 2.1%
rounding error.** The mint-ratio framing in §5b is the misleading one: the
executor mints 659 variables per trip and the solver eliminates **all** of them
(live world flat at 15), whereas the havoc mints 14 per trip and **7 survive for
the rest of execution**, because a demonically-produced unconstrained value is by
construction not determined by anything and there is nothing for the solver to
substitute. Compare live worlds rather than mints: at n=16 that is 15 against
127, an **8.5× larger** world, and declared-variable count is quadratic in lookup
cost (`lvar-lookup-cost-drivers.md`).

**Consequence for §6.3 — see §8.1, which first declared this annotation UNSOUND
and then WITHDREW that.** The deadness reasoning below is correct, and is both why
the register-set axis (§8) pays AND why the drop remains live: a state-dead
variable cannot resurface, and `occurs_check` proves it. Original text follows.

the "drop an unreferenced logical variable" annotation
is back to being the natural next lever, and for a sharper reason than before.
These binders are not merely numerous, they are *dead*: once trip k+1's havoc
replaces the register, trip k's `hv` is referenced by nothing at all, and it
survives only because `demonicv_prune` collapses on `block` and nothing else.
That is precisely the case the sketch in `Verifier.v` was written for. Still
unmeasured, and still to be measured before building: whether removing them
accounts for §3's residual exponent.

### Correction to the per-slot target set: x7 grows too, so it is SEVEN slots

`PLAN-annotinstr.md`'s 2026-08-24 entry names six growing slots (x5 x6 x10 x11
x14 x28) and says the other eight chunks are "EXACTLY 1.00x at every trip".
**x7 (T2) is not 1.00×: it goes 16 → 80 → 1,418 chars, a 17.7× steady-state
growth.** It is only 1.6% of the trip-3 total, which is presumably why it read
as flat, but it is a genuine loop-carried slot — at the loop head T2 holds the
previous trip's `sub T2, A1, T2`, which reads A1. Including T2 in `zz_all` was
therefore correct rather than harmlessly redundant, and the target set for this
program is seven registers, not six.

## 6. What this means

1. **`PLAN-annotinstr.md` Phase 4 is worth funding, and its predicted mechanism
   is the right one.** The plan's "λ ≈ 10.53 → 1 is an exponent change" is
   confirmed as to the exponent and overstated as to the 1.
2. **The measured payoff is for the SYMBOLIC side only.** This branch
   (`issue/annot-havoc-spike`) makes `sexec_ghost`'s `AnnotLemmaInvocation` case
   real and leaves `cexec_ghost`/`Adequacy` as stubs, so nothing here is proved
   sound yet. Phase 4 proper needs: `cexec_ghost` calling
   `CHeapSpec.call_lemma`; `rexec_ghost` via the ready-made
   `refine_compat_call_lemma` (`Refinement/Monads.v:1875`); and
   `cexec_ghosts_pure` DELETED in favour of an inductive `sound_cexec_ghosts`
   built from `call_lemma_sound` (`MicroSail/ShallowSoundness.v:91`, generic
   over the BI so it applies to the binary instance) plus the existing
   `lemSemCFGVerif` (`SpecIris.v:364`), discharged the way
   `iris_rule_stm_lemmak` does it (`BinaryInstance.v:196`, three lines).
3. **STANDS, with one addition — see §8.1.** `|Σ| = 15 + 7n` is correct and the
   binders really are dead. An intermediate version of §8.1 declared the drop
   annotation UNSOUND and that is **WITHDRAWN**: the side condition is about the
   PRESENT STATE, not the continuation's future, and `occurs_check` +
   `occurs_check_sound` already prove exactly it. What the drop needs is the
   carried state in hand, i.e. a step of `sexec_cfg_addr` rather than an
   `sexec_ghost` case. A second, independent lever on the same axis landed
   meanwhile: the havoc's REGISTER SET (§8), measured at 2.66× at n=16.
   Original text follows.

   **The next cost lever: the havoc's own dead binders.** `|Σ|` in the live world
   is `15 + 7n` with the havoc and a flat 15 without it (§5c) — the executor's
   own per-step mints are all eliminated by the solver, while a demonically
   produced unconstrained value never can be. Each trip's seven become dead the
   moment the next trip's havoc replaces them, and survive only because
   `demonicv_prune` collapses on `block`. So the "drop an unreferenced logical
   variable" annotation kind sketched in `Verifier.v` has a concrete, named
   target here. It is a HYPOTHESIS about §3's residual, not a measured cause;
   measure before building. (An earlier version of this record retracted the
   `15 + 7n` figure and declared the driver unidentified — see §5c for why that
   retraction was wrong.)

4. **Amdahl.** After the havoc, the per-trip term recurrence is gone as a driver;
   whatever remains is a *different* mechanism and this study does not identify
   it. Do not assume a second abstraction lemma helps.

## 7. Files and reproduction

Throwaway, gitignored, not in `_CoqProject` (`Example/ZZ*` convention).

| file | what |
|---|---|
| `Example/ZZAllocF_BASE.v` | definitions only — the baseline to subtract |
| `Example/ZZAllocF_{A,B,C,D}<n>.v` | one arm, one n, one `Eval` |
| `Example/ZZKind_D<n>.v` | the `26n+40` runs behind §4, `Time`d |
| `Example/ZZFuel_D{16,18,20}.v` | the `27n+60` re-runs that retract §4 |
| `Example/ZZSpikeCommon.txt` | the shared prelude the generators splice in |

```bash
OCAMLRUNPARAM='v=0x400' coqc -q -w none \
  -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  case_study/RiscvPmp/CFGVer/Example/ZZAllocF_D16.v 2>&1 | grep allocated_words
```

Requires this branch's `Machine.v` (`havoc_regs` constructor), `CFGVer/Spec.v`
(`lemma_havoc_regs`) and `CFGVer/Verifier.v` (the real `call_lemma` case); the
light chain through `Example/Prelude.vo` must be built first.

## 8. The havoc's REGISTER SET is itself a cost axis — and the "drop a dead variable" annotation cannot be built (2026-08-25)

**Finding, one sentence: havocing three registers instead of seven costs 2.66×
less at n=16 and is what makes br_divrem's real 31 trips reachable at all
(41.25 G words, `BLOCK`, 531 s).** §6.3's proposed "drop an unreferenced logical
variable" annotation is NOT retired by this — an intermediate version of §8.1
claimed it was unsound and **that claim is withdrawn**; it needs a different
INTERFACE (the carried state in hand) and the `occurs_check` machinery it needs
is already in the tree. See §8.1.

### 8.1 The sketched annotation, and a same-day CORRECTION of this section

**RETRACTED within hours of writing, 2026-08-25.** This section first concluded
that the `Verifier.v` "DROP AN UNREFERENCED LOGICAL VARIABLE" sketch is
**UNSOUND and off the table**. **That verdict is WRONG and is withdrawn — never
requote it.** The mechanism analysis below is correct and is retained, because it
does explain why the *shape the sketch proposes* fails; the impossibility
conclusion drawn from it does not follow. The error was conflating "the action
cannot inspect its continuation" with "the deadness fact is unavailable".

**Why the naive shape fails (this part stands).**

- `acc_subst_right` (`Worlds.v:381`) is the ONLY accessibility into a smaller
  context — every `acc_*` in `Worlds.v:320-411` was enumerated — and it requires
  a witness term `t`.
- The continuation runs at `w - x` but the action must return a `SymProp w`. The
  framework offers exactly TWO embeddings back, both visible in
  `assume_triangular` / `assert_triangular` (`Propositions.v:281,314`):
  `assume_vareq` and `assert_vareq`.
- `safe` (`Propositions.v:340,345`): `safe (demonicv x k) ι = ∀v, safe k`, while
  `safe (assume_vareq x t k) ι = (ι(x) = inst t → safe k)`. Under the `demonicv`
  the havoc already emitted, a drop composes to `safe k[x:=t]` — strictly weaker
  than `∀v, safe k` **unless `x ∉ fv(k)`**. `assert_vareq` instead demands a
  proof that an unconstrained demonic variable equals `t`, i.e. VC → `False`.

So a drop needs the side condition `x ∉ fv(k)`. **The withdrawn step was
concluding that condition is unavailable.** It is a condition on the PRESENT
STATE, not on the future: every term the continuation can ever build is built
from terms that exist now, so a variable occurring nowhere in the current state
cannot reappear in any later term. And the state is data.

**The machinery for exactly this already exists in the tree.**

- `occurs_check` (`Symbolic/OccursCheck.v:56`), reachable everywhere via
  `Base.v:68`'s mixin, returns `Some t'` precisely when the variable does NOT
  occur, handing back the term at the smaller context.
- Its law is the required fact verbatim:
  `occurs_check_sound : occurs_check xIn t = Some t' → t = subst t' (sub_shift xIn)`
  — "does not occur" ⟹ "is a weakening" (`OccursCheck.v:135`, via
  `OccursCheckSoundPoint`).
- Instances exist for Term, Formula (`Formulas.v:301`), Chunk
  (`Chunks.v:188`), list, Env, pair, option and Assertion
  (`Assertions.v:135-139`), so `SHeap = list Chunk` and
  `PathCondition = list Formula` are covered by composition.
- `Symbolic/Monads.v:97-99,130-133,163-164,195-197` **already occurs-checks the
  path condition and the heap together as a state** (for the debug-message
  instances). The state-level check is not hypothetical.
- The unifier already uses `occurs_check` for the structurally identical purpose
  — confirming `x ∉ t` before substituting `x := t`.

**What is genuinely left, and it is an interface question, not a soundness one.**
An opaque `SHeapSpec` action in `chunk_gc`'s shape receives `h` and `wco w` but
NOT the terms the continuation closed over — in `sexec_cfg_addr` those are `tbl`,
`exits`, `apc` and the outer postcondition. Each of those has an `occurs_check`
instance; they are simply not passed in. So the check is INCOMPLETE at that
interface, which is also why the refinement obligation (quantified over all
related continuations) cannot be discharged there. **The drop therefore belongs
as a step of `sexec_cfg_addr`, with the carried state in hand — not as an
`sexec_ghost` case.** Given an x-free state the `assuming`-vacuity objection also
dissolves: the concrete side at ι equals the concrete side at ι[x↦dummy], where
`assuming` is not vacuous.

**PHASE 0 RESULT (2026-08-25, and it went through TWO wrong verdicts before this
one — read `plans/PLAN-lvar-drop.md`, not this paragraph, for the design).** The
STANDALONE drop with a dummy witness is unprovable: `assuming` (`Worlds.v:755`)
requires an `ιpast` with `inst (sub_acc ω) ιpast = ι`, which for
`acc_subst_right t` forces `ι(x) = inst t (ι∖x)`, so with x unconstrained the
fibre over the generic ι is EMPTY, the hypothesis is vacuous, and the concrete
goal still has to be produced. (Nor is that repaired by the goal being
x-independent: entailment in `Pred` is POINTWISE in ι.)

**But the FUSED mint+drop IS provable, and it is proved.** Give the drop the
havoc's own freshly-minted variable as its witness instead of a dummy: the
composite `w ⊒ wsnoc w y ⊒ (wsnoc w y) - x` maps `x ↦ term_var y`, the fibre over
every ι is then inhabited by `(ι∖x) ► (y ↦ ι(x))`, and the operation is a faithful
RENAME rather than an erasure. `zz_fresh_witness` closes with `Qed`
(`plans/PLAN-lvar-drop.md` has the script; `assuming_acc_snoc_right`,
`UnifLogic.v:1248`, is what carries it — the enclosing demonic binder hands you
the continuation at any chosen value of the fresh variable, and you choose ι(x)).

Three consequences, all simplifications: **soundness needs NO side condition**
(a rename is unconditionally sound, so the operation can only be useless, never
unsound — the same risk profile as `chunk_gc`); `occurs_check` is still wanted but
only to pick genuinely dead candidates, so the fresh variable stays
unconstrained; and **net Σ growth per trip is zero**, since the havoc mints k
variables anyway and each can serve as the witness retiring one dead variable
from the previous trip. Only the crux is verified — the `□ᵣ`/`refine_four`
plumbing and the heap transport are not. Original paragraph follows.

**Why this is now the most valuable lever here, ahead of the packing below.** On
this program every havoced `hv` becomes state-dead the moment the next trip's
havoc consumes its chunk: the value is unconstrained so it is absent from `wco`,
and after the consume it is absent from the heap; `apc`, `tbl`, `exits` and the
postcondition all live over the contract's Σ and never mention it. So a working
drop takes the slope to **0 per trip — `|Σ|` FLAT** — where packing only reaches
1 per trip. That makes it a candidate for an actual exponent fix rather than
another factor, and it should be prototyped before the packing is built.
UNBUILT and UNMEASURED; the claim here is feasibility, not a result.

**The one part of the old verdict worth keeping as a design rule.** The contrast
with drop-chunks is still real and still instructive: throwing away a RESOURCE is
sound for any chunk by affineness and fails loudly at the next consume, whereas
throwing away a QUANTIFIER is sound only under a side condition and, if that
condition is not actually checked, silently changes which statement was proved.
Dropping a chunk costs completeness; dropping a binder without the
`occurs_check` costs soundness. The check is not optional bookkeeping — it is the
whole proof.

### 8.2 The axis, and the arms

| axis | states | what moves it |
|---|---|---|
| `havoc-breadth` | 3 / 4 / 7 registers | the `regs` list in the `havoc` ghost — nothing else |

| arm | registers havoced | rationale |
|---|---|---|
| R7 | T0 T1 T2 T3 A0 A1 A4 | = §1's arm D, re-run as a matched control |
| R4 | T2 A0 A1 A4 | the loop-carried set (T2 holds last trip's `sub T2,A1,T2`) |
| R3 | A0 A1 A4 | the recurrence carriers only (§5's conclusion) |

One axis, one knob: the three arm files differ from `ZZAllocF_D1.v` in exactly
the final `Definition t` line. **Protocol identical to §2 in every arm**
(`allocated_words`, `postprocess`'d tree via `Eval vm_compute`, no VC proof, no
`Qed`, fuel `27n+60`, one `Eval` per process), and the imports-only baseline was
**re-measured on this commit**: 611,601,212 words against §2's 611,564,884, i.e.
+0.006% — so §3's D column is directly comparable and is not being quoted across
a protocol or baseline boundary.

### 8.3 Results

Net G words. Protocol column deliberately present, per this project's own rule.

| n | R7 (7) | R4 (4) | R3 (3) | R3/R7 | protocol |
|---|---|---|---|---|---|
| 1 | 0.5685 | 0.4899 | 0.4647 | 0.817× | Eval, no Qed, 27n+60 |
| 2 | 1.0183 | 0.8179 | 0.7501 | 0.737× | ″ |
| 3 | 1.5998 | 1.2101 | 1.0803 | 0.675× | ″ |
| 4 | 2.3299 | 1.6719 | 1.4587 | 0.626× | ″ |
| 8 | 7.0788 | 4.3267 | 3.5150 | 0.497× | ″ |
| 16 | 28.9014 | 14.6691 | 10.8835 | **0.377×** | ″ |
| 31 | — | *killed mid-run* | **41.2498** | — | ″ |

**Every cell is `("BLOCK-vc-discharged", (1,0,0))`, checked explicitly** — n=31
included. So the term recurrence stays dead at three registers: the plain arm
was already 52.68 G at n=3, and R3 reaches 31 trips for 41.25 G.

**The control reproduces §3 at all six n** — recorded 0.5684 / 1.0183 / 1.5997 /
2.3299 / 7.0787 / 28.9014 against measured 0.5685 / 1.0183 / 1.5998 / 2.3299 /
7.0788 / 28.9014. Six for six. Independently, R3 at n=1 was run twice and
differed by 2,150 words in 1.076e9 (0.0002%), reconfirming the noise floor.

Local exponents per doubling (1→2, 2→4, 4→8, 8→16):

| arm | | | | |
|---|---|---|---|---|
| R7 | 0.841 | 1.194 | 1.603 | **2.030** |
| R4 | 0.740 | 1.031 | 1.372 | 1.761 |
| R3 | 0.691 | 0.960 | 1.269 | **1.631** |

**Held-out fits (required, and all three fail in the same direction).** Quadratic
on n = 2, 4, 8 predicting n=16: R7 25.08 vs 28.90 (**−13.2%**, reproducing §3's
published figure and thereby validating the fit method), R4 13.42 vs 14.67
(**−8.5%**), R3 10.18 vs 10.88 (**−6.4%**). For R3 a quadratic on n = 4, 8, 16
predicts n=31 at 36.40 against 41.25 actual (**−11.8%**).

So: fewer havoced registers is monotonically closer to quadratic, but **no arm is
quadratic and R3's exponent is still rising** (1.269 → 1.631 → 2.015 over 4→8,
8→16, 16→31). Quote the ratios, not a law.

### 8.4 Reading the axis

- **Dropping the three dead temps from the havoc is free money, and the case for
  it is now measured from both sides.** §5 found arm C (temps only) *actively
  harmful* at 1.941×; this section finds that removing those same temps from the
  full set is worth **2.00× at n=8 and 2.66× at n=16**, growing. Their term size
  is a symptom, they are recomputed from A0/A1/A4 inside every trip, and havocing
  them buys nothing while costing three binders per trip plus three
  consume/produce pairs.
- **Completeness moves the same way, not against it.** A havoced value carries no
  `secLeakvar` and is therefore treated as possibly-secret, so three fewer
  havoced registers is three fewer possibly-secret values. This axis is the rare
  one where cost and completeness are not in tension.
- **R3 beats R4 by 1.35× at n=16, so even a genuinely loop-carried register is
  better left alone here.** T2 does accumulate across trips (16 → 80 → 1,418
  chars, the correction recorded above), but that accumulation is *linear* once
  A1 is havoced, and one extra binder per trip costs more than it. **General
  rule: havoc the minimum set that breaks the recurrence, not every slot that
  grows.**
- **Peak footprint follows, which is what makes n=31 feasible at all.**
  `top_heap_words` at n=16: R7 1.693 G, R4 1.113 G, R3 0.968 G — R3 at n=8
  (0.636 G) peaks no higher than R7 at n=3. R3 at n=31 peaks at 1.947 G words
  (≈15.6 GB on a 14 GB box, so it swapped) and still finished in 531 s.

### 8.5 Before proposing anything further

1. **Predicted effect at the n that matters.** At br_divrem's 31 trips, R3 is a
   measured 41.25 G. R7 at n=31 was NOT measured; a quadratic on its n = 4, 8, 16
   gives 114.1 G, and since that fit underpredicts by ~13% it is a floor, so
   ≳2.8×. R4 at n=31 was killed mid-run and **the cause is not established** — no
   journal access on this box — though memory exhaustion is the obvious
   candidate given R3's own 15.6 GB peak. Do not record R4 at n=31 as an OOM
   without evidence.
2. **Constant factor or exponent change? A large factor, NOT an exponent fix.**
   R3's exponent is 1.269 → 1.631 → 2.015 and rising, the same shape as R7's
   one step lower. The wall moved; it was not removed.
3. **Still dominant after the fix? No — and this is the Amdahl point.** |Σ| is
   worth 2.66× at n=16, so it was never all of §3's residual, and after this the
   remaining ~2.6× superquadratic growth at n≥16 is a mechanism this study has
   NOT identified. §6.4 said not to assume a second abstraction lemma helps;
   that still holds.

**Next lever: the FUSED mint+drop (slope 0/trip), whose crux is proved** — §8.1's
Phase 0 note and `plans/PLAN-lvar-drop.md`. Packing stays as the fallback and is
strictly weaker (slope 1/trip, and it needs the wide-binder machinery the fused
drop does not): pack each trip's remaining fresh values into ONE
wide binder by slicing, exactly as `words_ctx` / `mem_class_width` already do
(`word-slicing-payoff.md` — worth 2.86× there).
Keep the precondition as separate `∃v_i` so the angelic consume still unifies per
chunk; make the postcondition a single `asn.exist "hv" (ty.bvec (k*xlenbits))`
with each register a `bvtake`/`bvdrop` slice. `bv.take_app` / `bv.drop_app`
(`Bitvector.v:947,974`) and `uop.bvtake` / `uop.bvdrop` (`UnOps.v:66-67`) all
exist, and `ValidLemma` stays existential intro over a `bv.app`. That takes the
slope from 3/trip to 1/trip — which is the floor for a LEMMA-only approach, since
a per-trip unconstrained value needs a per-trip binder and a lemma can only
weaken. It is NOT the floor overall: the drop (§8.1) is an executor step, not a
lemma, and reaches 0. Both are HYPOTHESES about the remaining cost, not measured
causes.

### 8.6 Files and reproduction

Throwaway, gitignored, not in `_CoqProject`. Generated from `ZZAllocF_D1.v` by
replacing only the last two lines, so nothing but the register list and `n` can
differ.

| file | what |
|---|---|
| `Example/ZZAllocF_BASE.v` | imports-only baseline, re-measured on this commit |
| `Example/ZZAlloc{R7,R4,R3}_{1,2,3,4,8,16,31}.v` | one arm, one n, one `Eval` |

```bash
OCAMLRUNPARAM='v=0x400' coqc -q -w none \
  -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  case_study/RiscvPmp/CFGVer/Example/ZZAllocR3_31.v 2>&1 \
  | grep -E 'BLOCK|ERROR|allocated_words|top_heap_words'
```
