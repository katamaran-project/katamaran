---
name: cfgver-scaling-diagnostics
description: >
  How to run and WRITE UP a CFGVer cost/scaling investigation — pinning down
  which mechanism makes a symbolic-execution example's cost blow up with
  trip count N, distinct from fixing it. Use this when asked to "diagnose",
  "investigate", "figure out the driver", "isolate the cause", or "write up"
  a cost/performance finding for a CFGVer loop or example, or before
  proposing a fix for a scaling wall so the fix targets the right mechanism.
  Covers the catalog of known cost-driver mechanisms (declared-chunk-count
  scaling with N, self-referential symbolic term growth, per-step
  instruction/term density, historically leaked duplicable chunks), the
  `diagnostics/` file convention (a completed causal record, distinct from a
  phased `plans/` document), and — the step most often skipped — how to
  design an ablation that isolates ONE candidate driver at a time instead of
  attributing a compound effect to a single cause. NOT for in-the-moment
  "why is this hanging right now" triage or the exact `allocated_words`
  measurement recipe — both live in `rocq-timeout-triage` (its Step 3
  already states the one-factor-at-a-time principle in miniature; this
  skill is the fuller treatment for when the output is a durable written
  record, not a quick unblock).
---

# CFGVer scaling diagnostics

A scaling *diagnostic* answers "which mechanism is responsible, and by how
much" for a specific example. A `plans/` document answers "what are we going
to build." They're different documents with different shelf lives — a
diagnostic's conclusion outlives whatever fix eventually gets chosen, so it
belongs in its own place: `case_study/RiscvPmp/CFGVer/diagnostics/`, sibling
to `plans/`. See `case_study/RiscvPmp/CFGVer/diagnostics/
key-schedule-loop2-cost-drivers.md` for a complete worked example of
everything below.

## Read these before measuring anything

Half of a new investigation is often already on disk. Check here first —
re-deriving a conclusion someone already established is the most expensive
possible way to start, and a *recurrence* of a known driver looks identical
to a fresh one until you compare.

| file (all in `diagnostics/`) | what it concluded |
|---|---|
| `key-schedule-loop2-cost-drivers.md` | TWO independent axes — declared-chunk **usage** (1 vs N genuinely-touched cells) and self-referential term growth — which is why any single-variant comparison here is a mix. As of the 2026-08-14 re-measurement the term axis is **closed** (`bop.mulx`, 0.98×). ~~declared-chunk count is the sole remaining driver (2.72× at N=16)~~ **corrected 2026-08-17: 82% of that is the LOGIC-VARIABLE count each `PVExist` cell mints, 2.80× → 1.32× with one shared variable; the chunk half is exactly bilinear in chunks × steps, and the *usage* axis is worth under 2%.** Also: every absolute figure predating 2026-08-17 in that file is 3–6× too high (§5.9's solver rule postdates it) — ratios mostly survive, `allocated_words` does not. **Re-measured 2026-08-18: the `|Σ|` axis is now CLOSED for declared cells** — `gen_contract_rel_classed` matches the weaker shared-variable arm to 0.07–0.59% at full statement strength, and it is an EXPONENT reduction (CD 1.43→1.72 vs CLS 1.11→1.22 over N=4→8→16), not a constant. What remains grows at exp ≈1.22 and RISING, and is **not identified** — that sweep was not run. The worked example for this whole skill, and for retraction discipline — twice over now. |
| `check-scalar-loop1-cost-drivers.md` | loop 1's accumulator is **cleared** — verdict confirmed at ~4–6% on a matched pair 2026-08-19, but **its own tables are RETRACTED as cross-protocol** (`Qed`+`solve_symbase_fetch` baseline vs `Admitted` no-feedback); never requote the 1.0038×/1.0136×. Absolutes superseded, and the imports baseline it tells you to subtract moved 434.8M → 604.3M. |
| `check-scalar-loop2-cost-drivers.md` | loop 2's `c` accumulation also small — but NOT because double-referenced accumulators are safe in general (`key_schedule_loop2`'s identically-shaped `H` genuinely is exponential). Per-iteration density is the primary driver here. **Its ~3.2% figure is RETRACTED 2026-08-19 as cross-protocol** (same `Admitted` no-feedback rig as loop1) and **re-measured at 1.0726× (7.3%)** on a matched pair — conclusion unchanged, but the real magnitude is 2.3× what it reported, so never requote ~3%. |
| `byte-classed-block-payoff.md` | the BYTE-granular classed block (`gen_mem_pre_rel_bytes_classed`, 2026-08-19) closes the last declared-cell `|Σ|` gap: **1.10× at 2 cells, 1.32× at 4, 1.77× at 8**, growing with cell count so more than a constant — but a held-out fit fails on BOTH arms (−14%/−23%), so **not** established as an exponent fix. Also the record that found the `Qed`/`Admitted` protocol trap recurring in the two loop records above. |
| `check-scalar-combined-cost-drivers.md` | re-concluded 2026-08-14: combining two loops costs **5.5–18.6×** the sum of the parts, splitting into a **symbolic-base amplification of 2.8–7.2×** (a concrete base removes it) and a residual **1.6–2.6× that is chunk-inventory cost**, dominated by instruction chunks. **§6.6 (2026-08-17) then retracted §6.5's chunk exponent**: chunk count is exactly linear, and the superlinearity is the LOGIC-VARIABLE count, quadratic and ~30–46× more expensive per unit (**that ratio is NOT a constant — `lvar-lookup-cost-drivers.md` §5.3 measures 19.5× at `|Σ|`=25, 65× at 89, 111× at 153, because the variable cost is quadratic and the chunk cost linear; never quote it without an `|Σ|`**) — read §6.6 before quoting any cost law from this file. Also the worked example for the PROTOCOL trap: a `Qed`+`solve_symbase_fetch` denominator against an `Admitted` numerator invalidated two tables. The old "~8–12%" is a pinned-sweep lower bound, superseded. |
| `lvar-lookup-cost-drivers.md` | 2026-08-19, answers Dominique's "is it variable LOOKUP?" hypothesis. **Chunk count spawns ZERO logic variables** (every structural count byte-identical over a 4× chunk range) and carrying one costs a flat **1.289 M words**; but the SAME chunk costs **16.1× more** when its variables sit 64 binders deeper, and the depth surcharge is `0.627 + 0.0195·chunks` G words (held-out **−0.0005%**). So chunks and lookup are NOT competing drivers — the dominant chunk-related cost IS a lookup cost, and they multiply exactly linearly. Pure lookup DEPTH at identical `|Σ|` is **1.16×–1.47×**; declared-variable COUNT is **quadratic** (held-out **+0.17%** at 4× beyond the fit range). Also: peak `|Σ|` is only 25 because the solver eliminates 1281 of 1293 mints, so the `|Σ|` quadratic is about DECLARED entries only, never per-step ones. |
| `prefix-length-cost.md` | 2026-09-04. **PROGRAM LENGTH is a QUADRATIC driver for a segment contract with an undecidable branch condition** — `93.81 + 4.05·P + 0.531·P²` M words in the number of NEVER-EXECUTED instructions sharing its table, held out at **+0.0024%** (the tightest fit in this directory), **26.9× over 64 filler instructions**. Needs the unknown counter: pinning it returns 1.42×, and the flat unrolled VC (1.60×), the pinned contract (1.42×) and a straight-line segment carrying three symbolic values (1.35×) are all linear and nearly free — so it is the *branch the solver cannot decide by computation*, not symbolic values and not length alone. **Every structural counter is byte-identical at every P** (236 nodes, 42 obligations, `|Σ|`=7, same branch structure), so the cost is TRANSIENT construction state, `base-k-hunt.md`'s finding again as an exact invariance. SCOPES `composition-payoff.md` §2.1 (1.155× is the straight-line value) and its ~90 M-per-segment law (that is K≈2; it is 2.53 G at K=66). Also: **conjunct order in the path condition is worth 1.74×**, and the 9.19× pinning ratio is not a constant but grows to 307× with length. Fix implied: per-segment table trimming, worth (K/k)², needing a sub-table faithfulness lemma. |
| `composition-payoff.md` | **VERDICT REVERSED 2026-09-05** (addendum). Pre-fix it found composition NEGATIVE — 6.4x worse on one loop, 7.30x on two, ~90 M per segment contract, "cut sparingly". After `cfdcc92f` a cut costs **7.10 M** (15.3x cheaper), composition is **0.56x** the flat VC, break-even is **~4.65 trips per cut** not ~71, and its central mechanism claim — "the expense is the unknown counter, 9.19x" — measures **1.006x**: the 9.19x was the infeasible branch that not knowing the counter left live, not the not-knowing. Flat arms reproduce to <=0.01% and are the calibration. Never quote the pre-fix numbers. |
| `base-k-hunt.md` | 2026-09-02, the NEGATIVE-results record for `Base(K)` (the 62%-of-footprint block from `env-lookup-cost-drivers.md` §9). Four candidates eliminated: `AMessage` snapshots (ablated, full rebuild — 1.7–2.1% of allocation, peak unmoved), the per-extension path-condition copy (mean |wco| ~10 formulas, share falling), `sub_wk1` construction (**Θ(|Σ|²) per extension** from unary `ctx.in_at`, 3.9% and the only one RISING), and term size. **The finding that matters: the ENTIRE finished VC is ≤2.6% of peak heap**, so `Base(K)` is not tree-reachable at all and no Coq-level traversal can find it — it is transient construction state, and needs OCaml heap profiling. Carries two method lessons: BOUND THE CONTAINER before dissecting contents (one term-node count would have excluded all four), and don't ablate for FOOTPRINT what merely ALIASES its bytes. Also self-corrects a `top_heap_words` quantisation error. |
| `ctx-fresh-cost.md` | 2026-09-02. `ctx.fresh` is **0.32–0.48%** of total cost and its share FALLS with K — the fresh-name scan is closed, and the catalog bullet that called it "the recommended next experiment" is retracted there. Also carries the first measurement-side evidence that per-mint work is **superlinear in `|Σ|`** (traffic grows 1.853× where cost grows 2.283× over K=162→206), pointing at `sub_comp` — indicative, not a fit. The worked example for bounding a candidate with two cheap measurements instead of building the fix. |
| `branch-refutation-payoff.md` | 2026-09-04, the A/B of `cfdcc92f`. **A live INFEASIBLE BRANCH was the prefix-length quadratic.** Teaching the solver to REFUTE a formula against one `wco` entry took the loop-body segment contract from `93.809 + 4.0506P + 0.530681P²` to `6.7197 + 0.029083P + 0.00014974P²` M words — quadratic coefficient **3544×** smaller, **275× at P=64** — and the surviving P-coefficients are *identical to the PINNED arm's* (0.13%/0.23%), so the branch-specific prefix cost is gone and only the generic table cost remains. Tax on contracts it cannot help is a **constant 10,228 words** (bit-identical at P=0 and P=64), 0.005–0.18%. Supersedes `prefix-length-cost.md`'s headline. Also the **Its §6 re-measures the SUB-TABLE payoff and finds the two levers ORTHOGONAL**: the synthetic countdown payoff collapsed 26.93x -> 1.36x, but all three REAL muladd payoffs (3.03x decidable, 3.63x pinned, 95.3x havoc'd) are unchanged to <=0.2%, because trimming buys the per-entry TABLE cost (3.25 M/entry on muladd) while refutation buys the BRANCH cost (which had inflated countdown's per-entry cost 998x). Keep the sub-table machinery. Also the worked example for an ablation that rules out the WRONG THING: deleting the guard leaves the cost unchanged and was read as "the branch is not the cause", but deleting the reason something is decidable and deciding it are opposite interventions — see its §4 retraction. |
| `word-slicing-payoff.md` | 2026-08-24, the payoff of instruction-word SLICING measured with the term-growth confound removed. **2.77×–2.86×** in allocated words (marginal 2.862×), vs the **1.61×/1.72×** wall-clock figure published on br_divrem — *larger*, because br_divrem's 10.54×/trip term growth sits in the denominator of a cost slicing cannot touch. Both arms exactly LINEAR in trips (held-out within 0.002%), so it is a constant factor, not an exponent change. `|Σ|` 17 → 4 with the node count moving by exactly the 13 removed `demonicv` nodes, so the win is variable carrying/lookup cost and not a smaller tree. Also the worked example for the **two-commit A/B** method below, and the counter-example to "payoff ∝ program length" — a SHORTER program (14 words vs 49) paid off MORE. |

Note what the two `check-scalar-loop*` records have in common: a mechanism
that is genuinely dominant in one example was measured near-zero in
another with the *same shape*. Cost-driver names transfer between examples;
their magnitudes do not.

## The core discipline: one axis at a time

The single most common way a cost diagnostic goes wrong is comparing two
variants that differ along **more than one** candidate mechanism, then
attributing the whole gap to the one you happen to be focused on. This
happens easily because it's natural to build a "fixed" version and an
"original" version and just diff them — but if the fixed version changed
two things, the measured gap is a *mix*, not a clean reading of either one.

The fix is procedural, not just a warning to be careful:

1. **Name every candidate mechanism as an explicit axis before measuring
   anything.** If you suspect both "N declared resources" and "a
   self-referential recurrence" might matter, that's two axes, not one
   investigation. Write them down as axes (`chunk-usage: 1 | N`,
   `term-growth: flat | growing`) before building variants.
2. **Design each variant to move exactly one axis relative to some other
   variant you already have.** Before trusting a comparison, list every way
   the two variants differ and confirm it's exactly the one axis you mean
   to be reading. A variant that silently differs in a second way isn't
   useless — it just isn't evidence about the axis you think it is.
3. **Name variants by their full axis-state, not an arbitrary label.**
   `N-used + growing-term` self-documents which axes it represents;
   `DISTINCT`/`SHARED`/`PADDED`-style names don't, and that's exactly the
   condition under which a two-axis comparison slips through unnoticed —
   an arbitrary name gives no reminder to check. This is worth doing even
   when you're confident there's only one axis in play, because a second
   one hiding is precisely what you can't see from inside the arbitrary
   name.
4. **Once every axis has an isolated reading, compositions are informative
   on their own.** If axis A alone gives a 2× effect and axis B alone gives
   a 4× effect, a variant with both should land near 8×, and if it doesn't,
   that mismatch is itself a finding (an interaction between the axes, not
   just two independent multipliers) — but you only notice a mismatch like
   that if you've actually got the two clean single-axis readings to
   compare it against.

`rocq-timeout-triage`'s Step 3 states the same idea in one sentence ("if
you suspect two factors changed at once... isolate them independently");
this is the fuller version, worth applying deliberately whenever the
answer is going into a written record, not just whatever gets you
unblocked right now.

## Known cost-driver mechanisms

These are the named mechanisms found so far, each pluggable into the
general executor cost law `heap_size × (α·S + β·S²)` (`S` = steps executed;
full history in `cfgver-executor`'s description) as a specific way one of
those terms grows with the trip count `N`:

- **Declared-chunk-count scaling with N — LINEAR, cheap to CARRY, expensive to
  LOOK THROUGH.** Carrying one chunk is **1.289 M words, flat**
  (`lvar-lookup-cost-drivers.md` §2), and a chunk spawns **zero** logic variables —
  measured structurally, every binder/vareq/`|Σ|`/lookup-weight count is
  byte-identical over chunks 0→16→32→64. But the same chunk costs **16.1× more**
  when the variables inside it sit 64 binders deeper (§5.2), because `persist`
  re-looks-up every occurrence at every world extension. At 64 chunks the carrying
  cost is 82 M words while the contribution to the depth penalty is 1.248 G —
  **15× larger**. **Design consequence: reduce the DEPTH, not the chunk count.**
  The rest of this bullet is the earlier, still-correct reading of the linearity:
  Isolated by moving chunk count at CONSTANT step count AND constant variable
  count (`check-scalar-combined-cost-drivers.md` §6.6): marginal cost per chunk
  is constant to four significant figures over a 4× range, held-out linear fit
  **0.00%**. **A previous version of this bullet said SUPERLINEAR (+64%
  marginal, `H^(1+ε)·S`) — that is RETRACTED**; the probe behind it grew chunks
  and logic variables together (four `ptstomem` chunks plus one `asn.exist` per
  padded word), and the variable was the whole effect. Never requote the +64%.
  **Steps are an independent co-factor**: pin the chunk count and cost is
  exactly linear in steps (held-out fit +0.00%), so halving executed steps
  halves cost regardless of chunks. On a diagonal where several factors scale
  with N this reads as super-quadratic — do not attribute it to any one alone.
  Fitting `c·H^a·S^b` on corner points of a grid where both grow together is
  ill-conditioned and returns nonsense (it gave a NEGATIVE chunk exponent); no
  `H^a` fit can work anyway, because the missing factor is `|Σ|` rather than a
  power of `H`.
  The precondition's resource list
  (`reg_specs`/`mem_specs`) is asserted once, up front, for the whole run —
  `gen_contract_rel` does not prune unused entries and does not grow the
  list incrementally as the loop executes. If a program's real data
  structure has `N` cells (e.g. a table being built one entry per trip),
  `heap_size` is `N` for the entire run, not amortized. Isolate this axis
  by holding the instruction body fixed and varying only whether the
  precondition/addressing genuinely touches `N` distinct chunks or 1.
- **LOGIC-VARIABLE COUNT (`|Σ|`) — QUADRATIC, and the biggest per-unit cost
  in the catalog.** One declared logic variable costs **~30–46× one declared
  chunk**, and unlike a chunk it makes every *other* transport more expensive:
  `env.lookup` is a linear walk (`Environment.v:154`), so substituting one
  variable occurrence is `O(|Σ|)` and `persist` of the heap at each world
  extension is `O(H · T · |Σ|)`. Measured from both sides — moving `|Σ|` at
  fixed chunk count turns a VC doubling-slope of 1.39 into 1.02
  (`plans/PLAN-byte-memory.md` §10, driver (C)), and moving both together is a
  clean quadratic in `|Σ|` with held-out error +0.20%
  (`check-scalar-combined-cost-drivers.md` §6.6), confirmed on a second
  independent rig where it is **82% of the whole declared-resource penalty**
  (2.80× → 1.32× at N=16 when N cells share one variable —
  `key-schedule-loop2-cost-drivers.md`, final section; that rig also shows the
  chunk half is *exactly* bilinear in chunks × steps, and that whether the cells
  are genuinely TOUCHED is worth under 2% — declaring them is the whole cost).
  This is where the apparent
  "chunk superlinearity" actually lived. **Split into DEPTH vs BREADTH 2026-08-19**
  (`lvar-lookup-cost-drivers.md` §4–5): at *identical* `|Σ|`, moving only the de
  Bruijn indices of the hot variables — K dead existentials placed before vs after
  the real precondition — costs **1.16×–1.47×**, linear in the shift (held-out
  +0.10%). That is the `env.lookup` walk alone. The remaining ~74% is breadth
  (`env.tabulate` per mint, `ctx.fresh`'s name scan, pc re-substitution) and is
  **entirely chunk-independent** (constant to 0.0003% across a 4× chunk range).
  Candidate for the quadratic specifically, from code and not yet isolated:
  `sub_comp` maps `subst` over an `Env` of `|Σ|` terms each doing an `O(|Σ|)`
  lookup, so composing two substitutions is `O(|Σ|²)` and the executor composes
  one per world extension — per-mint `tabulate`/`ctx.fresh` are only `O(|Σ|)` and
  cannot produce the quadratic. Sources of `|Σ|` growth: one
  `asn.exist` per unpinned (`PVExist`) spec entry, and per-step demonic
  variables. **A THIRD source, one demonic variable per instruction ADDRESS
  (the instruction words), was closed 2026-08-24** by slicing them all off one
  wide `bv (word*n)` variable — worth **2.86×** on a term-flat rig
  (`word-slicing-payoff.md`), and it is the cheapest kind of `|Σ|` fix there is:
  a pure re-encoding with no trusted-surface change, since
  `∀ W : bv (word*n)` and `∀ w_0..w_{n-1} : bv word` are in bijection under
  slicing. **The FIRST source is now fixed for the base-relative word-granular
  family: `gen_contract_rel_classed` (2026-08-18) emits one existential per
  publicness class instead of per cell, which is EQUIVALENT rather than weaker,
  and re-measured on the KSL rig it is an exponent reduction (1.72 → 1.22 at
  N=8→16), landing on the shared-variable arm's cost to within 0.6%. Use it by
  default there.** **The BYTE-granular
  block landed too (2026-08-19, `gen_mem_pre_rel_bytes_classed`,
  `byte-classed-block-payoff.md`), so declared-cell `|Σ|` is now closed in BOTH
  granularities — 1.10×/1.32×/1.77× at 2/4/8 declared byte cells, growing with
  cell count, though a held-out fit fails so it is NOT established as an exponent
  fix.** The one scope limit left: it does nothing about the
  per-step-demonic-variable source of `|Σ|`. (`gen_contract_param`'s concrete
  `mem_full_spec` block genuinely cannot be classed — width-index trap,
  `GenContract.v:536` — but all nine of its call sites pass `mem_specs = []`, so
  that block has no users and the limitation costs nothing.) Cheapest levers, in order: use the classed
  builder where it applies, pin what does not need to be
  existential (`PVConst` costs ~16–25× less than `PVExist` per entry), share
  one variable across several chunks where the values are genuinely related,
  and prefer FEWER LARGER symbolic objects over many small ones even when the
  small ones have smaller individual terms. **Isolate this axis** by holding
  chunk count and per-chunk term shape fixed and varying only how many distinct
  variables the chunk values project from.
- **FRESH-NAME GENERATION (`ctx.fresh`) — MEASURED 2026-09-02 AND CLOSED:
  0.32–0.48% of total cost, share FALLING with K. Do not fund a fix.**
  The mechanism is real — every mint builds the full name list of `Σ` and
  `List.find`s it, then on a base-name collision runs `max_with_base`, a second
  full scan with `split_at_dot` string parsing per element (`Context.v:707–714`),
  and per-step mints ALWAYS collide (`"a"`, `"np"`, `"na"` —
  `Verifier.v:188,501,507`) so they always take the expensive branch. It is just
  tiny: at K=206 on the muladd rig it is 12–17 M words against 3.64 G
  (`ctx-fresh-cost.md`), and over K=162→206 the traffic it generates grows
  1.853× where total cost grows 2.283×, so its share DROPS 0.59% → 0.48%. Two
  corollaries worth keeping: the obvious cheap fix (fuse `names` away) attacks
  the *small* half — the per-element cost is `split_at_dot`, not the cons cells;
  and "name by a counter" is not available at all, because `fresh` must be a
  pure function of the context (its result lands in a type, `wsnoc w (y∷σ)`).
  **RETRACTED, previous text of this bullet:** *"not yet isolated, cheapest
  possible fix … named as the recommended next experiment"*. The mechanism
  description was right and the recommendation was wrong; it was ranked on
  code-reading alone, and one afternoon of measurement — two microbenchmarks and
  two instrumented runs, no rebuild — would have settled it at any point.

- **PROGRAM LENGTH (instructions in the contract's table) — FREE for most
  contracts, QUADRATIC for a segment contract with an undecidable branch
  condition.** Two readings of the same axis, and which one applies is decided
  by one thing: whether the solver can settle the segment's branches by
  computation. If it can — a straight-line segment, a concrete trip count, a
  pinned counter — never-executed instructions cost **1.35×–1.60× over 64** of
  them, i.e. essentially linear and not worth attacking. If it cannot, which is
  the defining situation of a loop-invariant body contract, the same axis is
  `93.81 + 4.05·P + 0.531·P²` M words (`prefix-length-cost.md`, held-out
  **+0.0024%**), the quadratic term overtakes the linear one at **P ≈ 8**, and 64
  filler instructions cost **26.9×**. It is a FOOTPRINT driver too (41 MB → 1318
  MB net RSS), unusually for this directory. **The cost is transient**: every
  structural counter of the finished VC is byte-identical across the whole range,
  so no amount of pruning the result helps — only a smaller table does. **Isolate
  this axis** by padding BEFORE the segment (padding after moves the
  fall-through address and silently adds a second axis) and setting the entry pc
  past the filler so executed steps are held constant. Implied lever, not yet
  built: let a segment contract carry a SUB-TABLE of the program, worth `(K/k)²`
  and requiring a sub-table faithfulness lemma against `itable_rel`.
- **NON-SHORT-CIRCUITING `&&` / `List.forallb` in per-step code — a COST BUG,
  measured 22.7x on one call site.** Coq's `&&` is `andb`, a plain FUNCTION, so
  under the call-by-value `vm_compute` **both arguments are evaluated**; the same
  goes for `List.forallb`, which is `f a && forallb f l'`. Standalone probe:
  `andb cheap_false slow` **1.416 s** vs
  `if cheap_false then slow else false` **0.000 s**. Writing the match by hand
  (`if a then b else false`) is CONVERTIBLE to `a && b` but the VM takes exactly
  one branch. This bit CFGVer's `var_dead` (`Verifier.v`), an eight-conjunct
  `&&` guarding the dead-variable drop whose roots include the O(K) instruction
  table: every logical variable, at every drop attempt, at every step, forced a
  full walk of the whole program even after the variable had been found in the
  first root. Respelling it as nested `if`s and moving the O(K) root LAST took
  `drop_fuel=8` on the muladd rig from 44.233 G to 1.947 G net
  (**22.72x**), turning a 12.17x penalty into a 1.87x *saving*
  (`dropk-firing-payoff.md` ADDENDUM 2026-09-03). **Where to look:** grep `&&`
  and `List.forallb` in anything that runs per executor step, and check whether
  the conjuncts differ in cost by orders of magnitude — if they do, order them
  cheapest-first as nested `if`s. **The compounding factor to check alongside
  it:** an `oc_ok`-style wrapper that runs a CONSTRUCTIVE function and inspects
  only its constructor. `occurs_check : x in Sigma -> T Sigma -> option (T (Sigma - x))`
  REBUILDS the whole structure at the smaller context, and a boolean wrapper
  throws that copy away — so each forced conjunct was not a traversal but a
  copy-and-discard, which is exactly what `allocated_words` measures. **Cheap to
  fix, and the equivalence is a `reflexivity`-grade theorem** (`var_dead_andb`,
  256 subgoals), so there is no soundness argument to make and no trusted
  surface to move.
- **Self-referential symbolic term growth.** A register whose new value is
  computed from its *own* previous value every iteration (`H := f(H)`, not
  merely read twice within one iteration's formula) accumulates a nested
  symbolic term — roughly one extra node per iteration — so the term at
  step `k` is `O(k)`-sized, and processing an `O(k)` term at each of `N`
  steps sums to `O(N²)`, independent of chunk count. Isolate this axis by
  rerouting the self-referencing operand to a genuine constant (something
  that does not itself change across iterations) while changing nothing
  else about the instruction sequence.
- **Per-step instruction/term density.** Independent of both axes above: a
  loop body with many chained operations over largely-unconstrained
  (`PVExist`) operands can be expensive per iteration even at a small,
  fixed trip count, simply because each step's own symbolic term is large.
  Distinguish this from the self-reference axis above — a dense body can be
  expensive without any value feeding into its own next iteration at all.
- **Unrefuted pointer equality at a loop exit — one DEAD PATH PER TRIP,
  multiplying everything downstream.** A loop whose exit compares two
  base-relative pointers (`bne A0, A1` with `A0 = p+c₁`, `A1 = p+c₂`) forks at
  every trip, and the fall-through arm assumes `bvadd c₁ p = bvadd c₂ p`.
  For `c₁ ≠ c₂` that is provably false, but the solver does not refute it, so
  the dead branch is NOT collapsed to `SymProp.block` and **the entire
  remainder of the program is symbolically executed and verified underneath
  it**. Residual goals then obey exactly
  `A_first + A_second × T_first` (addresses owned by each loop; trip count of
  the FIRST one) — measured to the goal on three configurations in
  `check-scalar-combined-cost-drivers.md` §5.5. Linear, not exponential: one
  dead path per trip, no compounding. Three tells: cost is *positional*
  (reordering two loops changes which is multiplied), a single loop hides it
  (its dead paths hit the program end immediately, so the goal count looks
  clean while the paths are still built), and it vanishes at a concrete base
  (the equality computes to `false` on the spot). **Design rule: prefer a
  public pinned counter over a base-relative pointer compare as a loop exit.**
  `key_schedule_loop2` uses a counter and pays nothing; check_scalar uses
  pointer compares and pays 18–59× where KSL pays 3.4–4.9×.
- **Leaked duplicable chunks (historical, now fixed).** `encodes_instr`
  (`Sig.v`) was marked `is_duplicable := true`, and `heap_extractions` keeps
  duplicable chunks on consume rather than removing them — so a fresh
  existential minted every fetch never got cleared, growing the heap by
  exactly one chunk per instruction *step* (not per trip). Fixed by the
  landed chunk-GC (`plans/PLAN-chunk-gc.md`). Worth naming as a category:
  any predicate marked `is_duplicable` in `Sig.v` is a structural candidate
  for the same failure mode if it's ever produced fresh on a per-step,
  rather than per-address, basis — `grep is_duplicable` there before ruling
  it out on a new example.

A caution on terminology: this project has, at different times, tested a
*different* pattern under a similar-sounding name — a register read **twice
within one formula** (e.g. `c |= -EQ0(c) & CMP(...)`, `c` appearing twice in
one expression) — and found it not dominant for that specific reproducer
(see `cfgver-executor`'s description). That is not the same mechanism as
the self-referential-across-iterations pattern above (one read per
iteration, but nesting the *previous iteration's* value) — don't assume a
"term duplication isn't dominant" finding for one shape transfers to the
other without checking which shape you actually have.

## Reliable measurements

`allocated_words` (OCaml's own GC allocation counter) is the default — see
`rocq-timeout-triage`'s `references/allocation-probes.md` for the exact
recipe (`OCAMLRUNPARAM='v=0x400'`, subtracting an imports-only baseline, one
heavy proof/Eval per process, gating on `Finished transaction`). Don't
re-derive that mechanics here; read it before hand-rolling a probe.

**The metric is not where the errors come from.** Measured 2026-08-19: the same
probe run twice differs by **0.0008%** (9,226 words on 1.155e9). So one run per
point suffices, and a 1.06× ratio is ~7,500× the noise floor. The practical
consequence is worth internalising — **a wrong cost number here is essentially
never noise, it is a comparison-design error**: wrong denominator (protocol
mismatch, 1.81×), wrong baseline (stale imports figure, compresses ratios ~4%), or
wrong axis (two things moved). Every published-then-retracted figure in this
directory has that shape. So when a number looks surprising, re-examine the
comparison before re-running anything; repetition cannot fix a design error and
will just launder it.

**Re-measure the imports-only baseline on the commit you are measuring.** It is
example-independent — three sibling `Common` chains agreed within **313 words** —
but NOT commit-stable: it moved **434,833,198 → 604,283,692 (+39%)** in ~6 days.
The existing records instruct you to re-use their figure and are half right; the
half they omit costs 3.7–4.5% of any ratio you derive, in the *under*-claiming
direction.

Two things not yet in that reference, learned since: wall-clock is
unreliable not just from cache/scheduling noise but can be **actively
contaminated** by something as simple as the conversation itself pausing
mid-run (a process idling for an unrelated reason reads as enormous elapsed
time against negligible CPU-seconds — check the `u`/`s` split, not the
total, if a number looks absurd). And OS-reported peak RSS (`/usr/bin/time`)
can point the **wrong direction** entirely between two variants — prefer
OCaml's own `top_heap_words` (also in the GC stats dump) for a peak-footprint
question; it answers a different question from `allocated_words` (peak
simultaneous resident heap vs. total work ever done) and the two can
disagree in informative ways.

### Reading goal state during a diagnostic

Half of diagnosing a cost driver is dumping intermediate state, and Rocq's
goal-selection defaults quietly lie to you when there is more than one goal.
Each of these has produced a confidently WRONG reported result in this
project:

- **A period-terminated tactic acts on the FIRST goal only.** `tac1. tac2.`
  is not `tac1; tac2`. A `Show`/`idtac` dump written with periods inspects
  goal #1 and silently ignores the other fourteen — which on 2026-08-14 was
  read as "these are the goals my tactic failed on" when they were simply
  the untouched raw output, sending the session down a dead end. Same trap
  recorded earlier for `solve_vc. solve_symbase_fetch.`, which made an
  example look like it had a permanent discharge gap it did not have.
  Use `all:` when you mean all goals.
- **`all: idtac "X"` prints exactly ONCE regardless of goal count, including
  at zero goals.** It tells you the tactic ran, nothing more; as a goal
  counter it is pure noise and has manufactured a fictitious "1 residual
  goal at every N". For a count use
  `all: (let n := numgoals in idtac "count:" n)` — and note a BARE
  `numgoals` sentence reports 1 whatever the truth, because a plain tactic
  focuses one goal. For per-goal dumps,
  `all: (match goal with |- ?G => idtac G end)` does iterate correctly.
- **`Time (all: tac)` is a syntax error** — `all:` is sentence-level and an
  `Ltac` body cannot contain one. Time `(t1; t2)` jointly, or take a stage
  cost as a residual against the wall clock.
- **`n: Show.` does not parse**, because a goal selector takes a TACTIC and
  `Show` is a vernacular command. To inspect one goal's full context —
  hypotheses included, which is what distinguishes duplicated goals from
  genuinely different ones — use the vernacular `Show n.` on its own line.
  Diffing two goals' contexts this way is what identified the dead-path
  mechanism above; the conclusions alone were identical and said nothing.

Corollary worth internalising: if a dump shows N goals and your tactic
"fails", confirm which goals it was actually applied to before theorising
about why. Cheapest check is `all: try tac.` followed by a per-goal dump of
whatever survives.

## Before proposing a fix

Finding the dominant mechanism does NOT establish that fixing it is worth
building. Close that loop explicitly, because this project has twice paid
for a correct diagnosis that led to a fix which barely moved anything:

- **`select_last_k` (July 2026)** — an accumulator fold, algebraically
  correct, genuinely killed the `3^N` term-size wall it targeted. It bought
  **~12% at N=8**, and N=16 still did not finish, because the dominant cost
  at those N was a *separate* `O(steps²)` driver (a leaked duplicable heap
  chunk). Real proof engineering was spent, then reverted. **Sequel worth
  knowing (2026-08-14):** once that quadratic was fixed, the same wall *was*
  worth removing — a different rule (`bop.mulx`) took the term axis from
  3.7–4.7× to 0.98×, i.e. no measurable cost. So the lesson is about
  ORDERING, not about the diagnosis or the fix being wrong: fix the dominant
  driver first, then re-measure before funding the secondary one. Note also
  that the axis only read as fully closed once the *control* variants were
  re-measured on the same footing — a fix compared against its own stale
  pre-fix row could show "now linear" while the truth was "now free."
- **The world-GC** — reported as "2.24× → 10.67×, and the speedup GROWS
  with N". That growth was an artifact of dividing by a steeply superlinear
  baseline; measured on equal footing its real edge was a **constant**
  ~1.85× at N=8, shrinking as N fell.

So before writing a plan, state three things:

1. **Predicted end-to-end speedup**, from the fitted model, at the N you
   actually care about — not the N that was convenient to measure.
2. **Constant factor or exponent change?** A constant factor moves the wall;
   only an exponent change removes it. Say which, in those words. If a
   fix's own arm is only measured against a superlinear baseline, a "growing
   speedup" says nothing — compare arms on equal footing.
3. **Is this mechanism still dominant after the fix?** If it accounts for
   40% of cost, the ceiling is a 1.7× win and the other 60% becomes the new
   wall. Amdahl applies and is routinely forgotten.

If the honest answer is "a constant factor on a mechanism that is not
dominant", that is a legitimate result and belongs in the diagnostic — it
saves the next person the same detour. It is not a reason to inflate the
finding.

## Common mistakes checklist

- Trusting wall-clock, or OS RSS, across separate `coqc` processes.
- Not gating on `Finished transaction` appearing in the log before trusting
  a number — a variant that fails to compile reports only its baseline-level
  allocation, which reads as "this variant is free."
- Forgetting to subtract the imports-only baseline (it can be a large
  fraction of a small-N figure).
- More than one heavy `Eval`/proof per `coqc` process (later ones inherit
  an OCaml heap the earlier ones already grew).
- Concluding a growth law from one doubling, or a fit that stops too early —
  this project has more than once mistaken a small-N plateau for "it's
  flattening out" when a later crossover was just still ahead. Fit on two
  points and check a third you didn't use before calling something linear
  or quadratic.
- Comparing two variants without first listing every way they differ (the
  core discipline above).
- **Comparing across TACTIC PROTOCOLS — MEASURED AT 1.81×, and it is entirely
  the `Qed`.** Priced 2026-08-19 on one contract with only the `Proof.` script
  varying (`references/allocation-probes.md` §6b): `Qed` vs `Admitted` is
  **1.8096×**, while `solve_symbase_fetch` plus the period-vs-semicolon
  goal-selection difference is **0.99996× — free**. So the older phrasing of this
  rule ("a real `Qed` re-runs the executor *and* `solve_symbase_fetch` is extra
  work") bundled a 1.81× factor with a 0.004% one, and reads as a style note
  because of it. **1.81× exceeds most genuine findings** — the byte-classing win
  at 8 declared cells is 1.77× — so a protocol mismatch can impersonate the
  largest real effect in a study outright.
  History: it invalidated two tables on 2026-08-14 (understating a
  superadditivity ~1.4×), and **recurred on 2026-08-19** in
  `check-scalar-loop1`/`loop2`, whose no-feedback rigs are `Admitted` while their
  baselines are `Qed`; read as-is that yields a spurious **2.098×** for an axis
  whose true value is ~1.04–1.07×, and it was briefly mistaken for a regression.
  Copy an existing probe's `Proof.` line **verbatim** — better, generate the
  second probe from the first by `sed` so only the intended token can differ.
  **And put a PROTOCOL COLUMN in every results table.** That is the actual root
  cause of the 2026-08-19 recurrence: the numbers lived in a markdown table that
  did not record its protocol, while the protocol lived in `ZZ*.v` source, so
  comparing two rows *looked* complete. A figure recorded without its protocol is
  not a measurement.
- **Trusting `top_heap_words` at the low end.** It is the high-water mark of
  heap SIZE, quantized to OCaml's ~15% growth steps, and the multi-GB import
  closure means anything whose live set fits in the existing slack reads as
  byte-identical to the floor. That produced a confident "this variant is
  free at every N" for a variant whose allocation demonstrably grew 3×. Use
  `allocated_words` for cost; reserve peak footprint metrics for feasibility.
- **Trusting OS peak RSS for a ratio.** It saturates near the machine
  ceiling, compressing exactly the largest effects — it reported 3.5× where
  `allocated_words` reported 18.6× on the same pair.
- **Comparing two COMMITS by editing the working tree.** Don't. To price a
  landed change, build the old arm in a scratch COPY and switch load paths:
  `cp -r case_study/RiscvPmp $OFF/RiscvPmp`,
  `git show <old>:…/Verifier.v > $OFF/RiscvPmp/CFGVer/Verifier.v`, rebuild only
  the light chain there, then measure with `-Q $OFF/RiscvPmp Katamaran.RiscvPmp
  -R theories Katamaran`. `theories/` is shared and unchanged, so nothing heavy
  rebuilds (52 s for the whole CFGVer light chain, 2026-08-24). The working tree
  is never touched, the two arms cannot clobber each other's `.vo`s, and there is
  no restore step to forget. **Rebuild every file that `Require`s the one you
  swapped** — `Noninterference.v` requires `Verifier`, and a missed one shows up
  as a digest mismatch, not a wrong number. **Re-measure the baseline on BOTH
  arms**: the two baselines agreeing (1,441 words in 607 M) is what proves the
  import closures cost the same and the ratio is clean.
- **A sweep loop written with a shell variable is NOT exempt from
  `coqc-guard.sh`.** The hook waives its 3-builds-per-15-min rate limit for
  single-file probes by matching the literal string `CFGVer/Example/ZZ` in the
  command — so `for f in ZZFooN4 ZZFooN8; do coqc … Example/$f.v; done` is
  blocked mid-sweep, while the same builds with literal paths sail through.
  Write the paths out in full (several per Bash call is fine — the hook fires
  once per call). The denial lands mid-sweep and the budget only frees on a
  rolling 15-minute window, so it is worth getting right before starting.
- **Assuming an added EXIT prunes execution.** The exit/execute choice is
  `angelic_binary`, so an extra exit only grants permission to stop; the
  execute branch is still constructed and `vm_compute` still pays for it. An
  "exit early to skip the second half" probe measured 92–96% of the
  unmodified cost. To shorten a loop, minimise its trip count instead.

## Writing the diagnostic file

Location: `case_study/RiscvPmp/CFGVer/diagnostics/<short-name>.md`. Structure
that's worked well:

1. **One-sentence finding** at the top — the causal claim, in one sentence,
   before any setup.
2. **The experiment** — the axes, named explicitly, and a table mapping
   each variant's short name to exactly what it changed and which file
   implements it.
3. **Results** — the raw measurements, plus doubling ratios and the
   held-out-point fit check. Not optional: fit on the points you have minus
   one, then report the prediction error at the point you withheld. A fit
   quoted without one is a curve drawn through its own data.
4. **Reading the axes apart** — same-N, one-knob-changed ratios for each
   axis, isolated. This is the section that actually answers "which driver,
   how much," not the raw table.
5. **What this means** — tie the finding to a concrete next step (a fix
   candidate, a plan document, an open question), not just a restatement of
   the numbers.
6. **Files / reproduction** — throwaway probe files (not in `_CoqProject`,
   matching every other `ZZ*.v` probe convention) and the exact commands to
   rerun them.

Keep it information-dense rather than narrating the investigation's
history — the reader wants the causal picture and how to reproduce it, not
a blow-by-blow of what was tried in what order.

### When a later measurement overturns an earlier one

It will. Several headline figures in this project's record have been
refuted by a subsequent, better-controlled run — "the curve bends /
exponent 1.05" (an artifact of stopping the series at N=8), and "heap size
is measured NOT to be a driver (0.95×)", which was wrong and had already
been used once to dismiss the leak that turned out to BE the driver.

**Mark the old claim retracted in place; never silently delete or edit it.**
A reader who remembers the old number needs to find out it was wrong, and a
figure that merely vanishes looks like it is still true somewhere else. In
practice:

- Leave the original text, prefixed `RETRACTED <date>:`, with one line on
  *what specifically* was wrong — the N range, the confound, the baseline.
  Distinguish "the numbers were real but the conclusion doesn't follow"
  from "the measurement itself was bad"; they have different lessons.
- If a figure is quotable-but-wrong, say **"never requote"** explicitly.
  This is what stops it being cited from the old section by a future
  session that skimmed.
- Retract the *conclusion*, keep the *measurements* — later work often
  reuses the raw numbers on a corrected footing.
- Correct the memory note and any `plans/` doc that cites the figure in the
  same commit, per this repo's "docs travel with code" rule. A retraction
  that lives in only one of three places is how the bad figure survives.
