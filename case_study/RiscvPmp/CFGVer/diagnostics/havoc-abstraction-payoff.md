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
established here — do not quote one.** It is very nearly free in variables, though: §5b measures
the lemma minting 7 demonic + 7 angelic variables per trip against a baseline of
659 per trip (+2.1%), with **zero** surviving `postprocess`. (An earlier version
of this record said `|Σ| = 15 + 7n` and blamed the residual growth on it; that
is RETRACTED in §5b — it was an artifact of fuel-starved runs.)

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
binders, at every n). The havoc's variables cost nothing in the final VC.

### RETRACTED: `|Σ| = 15 + 7n` as the explanation for §3's residual growth

§4 reported `binders = 15 + 7n` and §6.3 called it "the only quantity known to
grow per trip in arm D" and hence the likeliest home of the residual
superquadratic cost. **Both the number and the inference are withdrawn.**

- The number came from runs whose execution died in `error` on exhausted fuel.
  Prune cannot collapse a binder spine that does not end in `block`, so those
  binders survived as an artifact of the broken configuration. In a healthy run
  the count is **15, flat, at n=1, 2 and 3** — identical to the no-havoc arm.
- A related printing artifact, worth knowing before trusting any postprocessed
  dump: the debug payload at trip 2 references `hv.4` while no `demonicv "hv.4"`
  remains in the tree. `AMessage` is opaque to prune, so a message can name a
  variable whose binder prune has already dropped.
- The inference is therefore dead too: 14 extra mints per trip on a baseline of
  659 cannot produce §3's residual. Whatever drives that is in the executor's
  own per-step mints, and this study does not identify it. **Do not cite the
  havoc's variable count as a cost driver, and do not treat the
  "drop-an-unreferenced-variable" annotation as its fix on this evidence.**

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
3. **The next cost lever is NOT identified.** ~~`|Σ| = 15 + 7n` is the only
   quantity known to grow per trip in arm D~~ — RETRACTED, see §5b. The havoc
   adds 2.1% to per-trip mints and nothing at all to the final VC, so it cannot
   be what drives §3's residual. The remaining candidate is the executor's own
   per-step mints (265 demonic + 394 angelic per trip), but peak `|Σ|` during
   execution was not measured here and the "drop an unreferenced logical
   variable" annotation has no evidence behind it on this program. Measure
   before building anything.
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
