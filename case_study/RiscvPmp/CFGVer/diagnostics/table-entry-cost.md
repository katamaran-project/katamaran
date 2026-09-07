# Why the VC cost scales with the number of instruction-table entries

**Status: ANSWERED (2026-09-07).** §3 is the answer — **89% carrying cost, 8% exit
overshoot**. §1–2 are the route; §3a retracts an earlier revision of §3 that had
it backwards. Three refuted hypotheses and one arithmetic error are kept
deliberately, all four from fitting a mechanism to two data points. The mechanism inventory in §1 is from
the code and is settled. The fix §1b proposed was implemented, measured, and
**buys nothing** (§2). The per-entry charge is real and remains UNEXPLAINED — §1's
three named mechanisms do not account for its magnitude, and §2 rules the
cheapest of them out entirely.

Question it answers: `branch-refutation-payoff.md` §6.1 measured a
**branch-independent per-table-entry charge** — 3.25–3.35 M words/entry on
muladd, 0.038 M/entry on the post-fix countdown rig, and **161.2 M/entry** on
the havoc'd muladd arm. That record named the charge but never explained it.
This one asks *why a contract pays for instructions it never executes*, and
whether the charge is necessary.

## 1. The three per-entry charges, from the code

All three are in `Verifier.v` and all three run per executed step.

| # | site | shape | per step |
|---|---|---|---|
| 1 | `lookup_instr` (`Verifier.v:637`) | `List.find (fun '(t,_,_) => Term_eqb (peval apc) (peval t)) tbl` | one walk to the matching entry; a **full** K walk on a miss (which every fall-through past the end is) |
| 2 | `persist_itableW` (`Verifier.v:395`) | `List.map` over all K entries, `persist__term` on **both** term columns | ~3× (θ0 from `chunk_gc`, θd from `drop_dead`, and `step_after_drop`'s θ1∘θ2∘θ3), plus one per successful drop |
| 3 | `var_dead` → `itableW_free` (`Verifier.v:745`) | `forallb_sc` of two `oc_ok`s over all K entries | once per drop attempt that gets past the cheap roots |

`is_exit` (`Verifier.v:642`) has `lookup_instr`'s exact shape over the exit
table, which is small in every current program.

### 1a. Why (2) is not a no-op even though the table never changes

The instruction table is **semantically constant for the whole run** — same
addresses, same words, same instructions at step 1 and step 200. It is rebuilt
several times per step anyway, because its terms are indexed by the world's
variable context and every world extension renumbers that context:

`persist__term t θ = subst t (sub_acc θ)`, and for a demonic mint
`sub_acc acc_snoc_right = sub_wk1` (`Terms.v:785`), which is
`env.tabulate (fun ς ςIn => term_var (ctx.in_succ ςIn))`. So weakening maps
every `term_var` to *the same variable with one more `in_succ` wrapper*. The
result is structurally identical to the input up to de Bruijn renumbering, and
producing it is a full deep copy whose leaves each pay an `O(|Σ|)` `env.lookup`.

This is a pure indices-vs-levels artifact: with `ctx.In`'s zero at the **snoc**
end, adding a variable shifts every existing index. Had the context been indexed
from the front, `persist` of a weakening would be the identity.

(`base-k-hunt.md` §"sub_wk1" separately measures *constructing* `sub_wk1` at
Θ(|Σ|²) per extension — that is the per-extension cost, orthogonal to the
per-entry cost here.)

### 1b. `peval apc` was recomputed once per entry — a plain loop-invariant bug

In (1), `peval apc` sat **inside** the `List.find` predicate, so it was
recomputed for every entry visited, at every lookup, at every step. Same in
`is_exit`'s `existsb`. The comparison's left argument does not mention the
entry, so this is pure waste, and it makes the walk cost
`K · cost(peval apc)` rather than `cost(peval apc) + K · cost(peval t)`.

Fixed 2026-09-06 by hoisting into a `let`. The `let` is zeta-convertible to the
old body, so no downstream proof sees a different term.

**Hypothesis this suggests, and the reason it is worth testing rather than
assuming:** if the dominant per-entry charge is `K · cost(peval apc)`, then the
otherwise-unexplained **48× undecidable-branch multiplier**
(`branch-refutation-payoff.md` §6.1: 161.2 vs 3.35 M/entry, *same program, same
cut, same table*) is not a branch phenomenon at all — it is the ratio of
`peval` cost on a havoc'd `T0`-derived pc term versus a pinned one, multiplied
by K. Havocking `T0` is exactly what makes the pc term large.

**Caveat, stated up front:** a back-of-envelope count does not close the gap.
A table entry is ~7 term nodes; at |Σ|≈30 and ~11 table traversals per step, the
traversal charges above come to 10²–10⁴ words per entry per segment, against a
measured 3.35 **M**. So either `peval` on these terms is far more expensive than
its term size suggests, or a fourth K-dependent mechanism has not been named.
The A/B below is what distinguishes those.

## 2. A/B: hoisting `peval apc` — NO EFFECT, hypothesis refuted

Every arm lands within 0.1% of its pre-hoist value, with deltas scattered in
sign. `peval apc` is cheap; recomputing it once per visited entry costs nothing
measurable even at P=128, where `List.find` calls it ~129 times per lookup.

| arm | pre-hoist | post-hoist | delta |
|---|---:|---:|---:|
| `pbody 0` | 6.7197 M | 6.7209 M | +0.017% |
| `pbody 16` | 7.2281 M *(fit)* | 7.2280 M | −0.001% |
| `pbody 32` | 7.8071 M *(fit)* | 7.8047 M | −0.031% |
| `pbody 64` | 9.1943 M | 9.1878 M | −0.071% |
| `pbody 128` | 12.8956 M *(fit)* | 12.8829 M | −0.098% |
| `ZZSegTrimP` (15 entries) | 339.37 M | 339.348 M | −0.007% |
| `ZZSeg2P` (282 entries) | 1232.53 M | 1232.250 M | −0.023% |
| `ZZSegTrim` (havoc'd, 15) | 456.36 M | 456.354 M | −0.001% |

Muladd per-entry cost from the measured pair: (1232.250 − 339.348)/(282−15) =
**3.344 M/entry**, against 3.345 published. Unchanged.

**The rig validates.** All five `pbody` points reproduce
`prefix-length-cost.md`'s post-branch-fix law `6.7197 + 0.029083·P +
0.00014974·P²` to ≤0.1%, including the three points that were previously only
interpolated — so this run also converts those from fit to measurement.

**Method caveat.** This is measured against the `branch-refutation-payoff.md`
record rather than a same-session revert-and-rebuild A/B. That record's §1
establishes the rig reproduces on this machine to ≤0.013%, and the agreement
above is at that level across eight arms, so the negative conclusion is safe.
A matched A/B would cost one more CFGVer rebuild and was not run.

### 2a. What this kills

- The `K · cost(peval apc)` model of the per-entry charge.
- With it, the conjecture in §1b that the **48× undecidable-branch multiplier**
  is a `peval`-cost ratio. That multiplier is still unexplained.
- The hoist is kept anyway — it is strictly less work and zeta-convertible — but
  it should not be described as a fix for anything.

### 2b. What is left standing, and the size of the hole

§1's remaining mechanisms are `persist_itableW` (charge 2) and `itableW_free`
inside `var_dead` (charge 3). Both are real O(K)-per-step walks. Neither is
close to big enough on a term-size count: ~7 term nodes per entry, |Σ|≈30,
~11 table traversals per step gives 10²–10⁴ words per entry per segment against
a measured 3.34 **M**. A fourth K-dependent mechanism has not been named.

Note also the rig's **quadratic** term (0.00015·P², 6.7% of cost at P=64, 24% at
P=128) at *constant executed steps*. None of the three named mechanisms is
quadratic in K. That is a second thing §1 does not explain.

## 2c. The charge is PER STEP, and §2b's "hole" was my own arithmetic error

`pflat P N` executes `2N` instructions against a `P+2`-entry table, so measuring
the P-slope at two N separates a per-step per-entry charge from a one-off one.

| N | executed steps | `pflat 0 N` | `pflat 64 N` | P-slope |
|---:|---:|---:|---:|---:|
| 4 | 8 | 9.522 M | 14.645 M | **0.0801 M/entry** |
| 16 | 32 | 27.863 M | 45.684 M | **0.2785 M/entry** |

Slope ratio **3.48×** for a 4× step increase. Fitting `slope(N) = a + b·N`:
`0.0139 + 0.016534·N`, i.e. **83% (N=4) to 95% (N=16) of the per-entry charge is
per-step**. It is in the executor's per-step table handling — `persist_itableW`,
`lookup_instr`, `itableW_free` — not in construction or `postprocess`.

Per entry per executed step on this rig: **~8,270 words**.

**§2b's claimed three-orders-of-magnitude hole does not exist.** It compared a
per-*step* estimate against a per-*segment* measurement. Corrected, the
back-of-envelope for `persist_itableW` (~7 term nodes × 2 columns × ~11
traversals/step, each leaf an `O(|Σ|)` `env.lookup`) lands within ~1.5× of the
measured 8,270. No fourth mechanism is needed.

### 2d. The model this leaves, and why the table is a heap chunk in disguise

`pflat`'s context is `[ctx]` — essentially no logic variables — so 8,270
words/entry/step is the **floor**. Muladd's 3.344 M/entry over ~20 steps is
~167,000 words/entry/step, about **20× the floor**, on a program carrying
roughly that many more logic variables.

`persist__term` costs `O(term nodes × |Σ|)`, because every `term_var` leaf pays
an `env.lookup` walk. So the model is

> per-entry cost ≈ (executed steps) × |Σ| × c

which is *precisely* `lvar-lookup-cost-drivers.md`'s result for heap chunks —
"the same chunk costs 16.1× more when its variables sit 64 binders deeper,
because `persist` re-looks-up every occurrence at every world extension".

**The instruction table is the same phenomenon as a heap chunk and was never
counted as one.** It is persisted at every world extension, its cost is
`O(entries × |Σ|)` per extension, and no entry in the cost-driver catalog covers
it.

This also gives the **48× havoc'd multiplier** a mechanism rather than a name:
havocking mints logic variables, `|Σ|` rises, and every table entry pays for it
at every step.

### 2e. Structural counts: the charge produces ZERO output

`zz_stats_raw` (`ZZLvarInstrCommon.v`) on the raw VC:

| rig | entries | binders | vareqs | max \|Σ\| | Σ-integral | nodes |
|---|---:|---:|---:|---:|---:|---:|
| `pflat 0 4` | 2 | 175 | 173 | 6 | 459 | 575 |
| `pflat 64 4` | 66 | **175** | **173** | **6** | **459** | **575** |
| `pbody 64` | 66 | 69 | 66 | 7 | 244 | 225 |
| `zzsegtrim` | 15 | 371 | 345 | 32 | 9839 | 2374 |
| `zzseg2` | 282 | 489 | 464 | 32 | 13109 | 3454 |

**The two `pflat` arms are structurally IDENTICAL — every counter byte-identical
— while costing 9.522 M and 14.645 M (+54%).** 64 extra table entries buy
exactly nothing and cost half again as much. This is the finding: the per-entry
charge emits no tree nodes, mints no variables, and changes no counter, so it
can only be the per-step traversals (`persist_itableW`, `lookup_instr`,
`itableW_free`).

Note the muladd pair is NOT like this — its tree does grow with the table
(2374 → 3454 nodes) while cost grows far faster (339 → 1232 M). Peak `|Σ|` is 32
either way, so table size does not drive `|Σ|`.

### 2f. The floor-vs-muladd gap: it is the `|Σ|` axis, not the symbolic base

Per entry per executed step: `pflat` **~8,270 words**, muladd **~167,000**
(3.344 M over ~20 steps) — a **20×** gap. Two axes differ.

1. **`|Σ|`.** Mean `|Σ|` (Σ-integral / nodes) is 0.80 on `pflat` and ~3.8–4.1 on
   muladd — 4.8×. Linear in `|Σ|` gives 4.8×; quadratic gives ~23×, and
   `lvar-lookup-cost-drivers.md` §5 measured declared-variable count as
   quadratic. **20× fits the quadratic.**
2. **Concrete vs symbolic base.** `pflat`/`pbody` are based at
   `term_val (bv.of_N 0)`, so `table_of_list`'s `peval_bvadd (term_val off) base`
   folds to a single `term_val` and their entries carry *no variable
   occurrence*. Muladd is based at `term_var "p"`, so all 282 entries carry one.

**Axis 2 is already measured elsewhere and is SMALL.**
`check-scalar-combined-cost-drivers.md` §5.8 named it as candidate 2, "symbolic
address terms … every address is `bvadd (val off) p` rather than a literal", and
isolated it with arms A (symbolic base, bound obligations deleted at source) vs
C (concrete base). Post-`try_fetch_bound` that residue is the **1.55–1.73×**
base penalty at N=4/8/16/32 — rising with N, but not a major multiplier. It
therefore cannot account for a 20× gap, and **axis 1 is the explanation.**

Two caveats on that reuse: §5.8's ratio is whole-program on the check_scalar
rig, not per-table-entry, so it bounds the effect only loosely here; and it is a
different program. But the expected effect size is 1.5–2×, not 20×.

**Do not re-run a symbolic-base isolation arm for this question.** It was run
2026-08-17.

### 2g. What §5.8 got right, and the one word to revise

§5.8's "NOT removable by any VC work" is correct: no solver rule or obligation
discharge can make `bvadd (val off) p` into a literal. That is why the bound-VC
fix, which reached 99.5% of its own ceiling, left this behind.

It is removable by *representation* work, which is a different lever — §3. That
matters less than it did an hour ago, since §2f puts the prize at ~1.5–2× rather
than 20×, but it is not the dead end the phrasing suggests.

## 2h. FOUND IT: the word column's O(K²) nesting is the entire quadratic

Matched same-session A/B, both sides measured today on the same tree, control =
§2's post-hoist run. Ablation is `prefix-length-cost.md` §3.2b's, re-run in the
POST-branch-refutation regime: `words_of_slice`'s recursive
`take (drop^i W)` replaced by `List.repeat (dtake word (words_width n') W) (S n')`,
so every entry shares the depth-0 slice and the column is O(1) term nodes
instead of `K(K+3)/2`. Length preserved, so `zip_words` cannot truncate.
UNSOUND (every address gets the same word) — measurement only, reverted after.

| P | control | ablated | Δ | share of K-dependent cost |
|---:|---:|---:|---:|---:|
| 0 | 6.7209 M | 6.7153 M | −0.0056 M | — |
| 16 | 7.2280 M | 6.9354 M | −0.2926 M | **56.6%** |
| 32 | 7.8047 M | 7.1494 M | −0.6553 M | **59.9%** |
| 64 | 9.1878 M | 7.5798 M | −1.6080 M | **65.0%** |
| 128 | 12.8829 M | 8.4600 M | −4.4229 M | **71.7%** |

**It is an EXPONENT change, not a constant.** Marginal cost per entry:

| P | control | ablated |
|---:|---:|---:|
| 16 | 0.03170 | 0.01376 |
| 32 | 0.03387 | 0.01357 |
| 64 | 0.03855 | 0.01351 |
| 128 | 0.04814 | 0.01363 |

The control rises (the quadratic); the ablated arm is **flat to 1.8% across an
8× range in K**. A fit on P ∈ {0,16,32} gives the ablated quadratic coefficient
as −1.2×10⁻⁵ — indistinguishable from zero, slightly negative. The law goes

    6.72 + 0.0295·P + 0.000136·P²   →   6.72 + 0.0136·P

so the nesting is the whole quadratic AND about half the linear term.

### 2i. This INVERTS `prefix-length-cost.md` §3.2b, and why

§3.2b ran this exact ablation on 2026-09-04 and got **−0.07% at P=64**,
concluding "**do not 'fix' the word-slice nesting**" and drawing the method
lesson that matching exponents are not causation. That was correct *at the
time*: the quadratic coefficient was then **0.5306**, of which ~99.97% was
un-refuted branch cost. `cfdcc92f` (2026-09-05) removed that, leaving
**0.00014974** — 3544× smaller. The word column's contribution barely moved in
absolute terms (1.717 M then, 1.608 M now, at P=64); it went from 0.07% of the
total to 65% of the K-dependence because everything around it disappeared.

**General lesson, and it applies to every other "not the cost" verdict in
`prefix-length-cost.md` §3.2:** an ablation's verdict is relative to the
denominator that was there when it ran. `cfdcc92f` changed that denominator by
3544×. Any §3.2 candidate dismissed at a sub-percent share should be re-run
before being trusted — the numerator was never the thing that changed.

### 2j. What this leaves

The residual K-dependence after the ablation is **exactly linear at ~0.0136
M/entry**, which is the §1 structural cost — `persist_itableW`'s list rebuild,
`itableW_free`'s walk, `lookup_instr`'s `List.find`. That is the part base+offsets
(§3) addresses, and it is now known to be linear, so it is a constant-factor
target, not an exponent one.

## 3. THE ANSWER: 89% carrying cost, 8% exit overshoot

A seven-point table-size sweep (`Example/ZZK_*.v`: `List.firstn K (List.skipn 55
zzmuladdfulln2_instrs)`, K = 15…75, everything else fixed, all `Qed`), plus node
counts at three of those K. K=15 is exactly the executed segment (offsets
220..276); the declared exit is at 280, so K≥16 puts an instruction AT the exit.

| K | net | Δ | per entry | raw nodes |
|---:|---:|---:|---:|---:|
| 15 | 339.371 M | — | — | 2374 |
| 16 | 349.580 M | 10.209 | 10.21 | — |
| 18 | 378.155 M | 28.575 | 14.29 | — |
| 20 | 413.524 M | 35.369 | **17.69** | **3454** |
| 25 | 428.688 M | 15.164 | 3.033 | — |
| 35 | 459.089 M | 30.401 | 3.040 | — |
| 75 | 581.068 M | 121.979 | **3.049** | **3454** |
| 282 (= `ZZSeg2P`) | 1232.250 M | | | **3454** |

K=15 reproduces `ZZSegTrimP` to 0.007%, so the sweep is calibrated.

**Two regimes, and the node counts separate them exactly.**

1. **K=15→20 — EXIT OVERSHOOT, 74.15 M (8.3%), +1080 nodes.** The segment
   executes 15 of its 20 fuel, so ~5 remain; with an instruction at the exit
   address the executor spends them running PAST the declared exit. Marginal
   cost 10–18 M/entry. Bounded by leftover fuel, and the bound fits to the
   instruction.
2. **K>20 — CARRYING COST, 3.033/3.040/3.049 M/entry, ZERO extra nodes.**
   Byte-identical node counts at K=20, 75 and 282 (279/191/214/275/0/0/661/586/
   586/662). These entries sit at offsets 300–516, unreachable on the remaining
   fuel, produce nothing, and cost 3.04 M each with no ceiling.

Model closes on the full 892.9 M gap to **2.5%**:
`74.15 (overshoot) + 207×3.04 (suffix) + 55×3.04 (prefix) = 870.6`.

### 3a. RETRACTION: this file's own previous §3

An earlier revision of this section (commit message included) concluded
**"reachable control flow, not carrying cost"**. That is **backwards** — it is
89% carrying cost. The error was reading the +4.04 nodes/entry from the *two*
available table sizes as evidence that exploration was the whole mechanism. The
node growth is entirely confined to the fuel-reachable window; the cost is not.
The sweep is the seven points that should have preceded the conclusion, and it
is the third two-point mechanism-fit to fail in this investigation (see §2a,
§2f).

Consequently retracted from the previous revision:
- "base+offsets is NOT worth doing (~0.4%)" — **wrong**; it attacks the 89%.
- "the padding rig is unrepresentative IN KIND" — **wrong**; it measures the
  right mechanism (carrying cost) at 224× too small a magnitude. See §3b.
- "the sub-table mechanism is control-flow pruning" — **wrong**; it is
  overwhelmingly table-carrying reduction, with an 8% pruning bonus.

Upheld from the previous revision: the machinery is sound (identical
postprocessed VCs), and the word-column verdict (§2h/§2i).

### 3b. Why the pad rig is 224× too small — the `|Σ|` axis, again

| rig | per entry | steps | per entry per step | peak `\|Σ\|` |
|---|---:|---:|---:|---:|
| `pbody`/`pflat` (word-column-ablated, pure carrying) | 0.0136 M | ~2.5 | 0.0054 M | 7 |
| muladd, K>20 (pure carrying) | 3.04 M | ~20 | 0.152 M | 32 |

**28× per entry per step against a 4.6× `|Σ|` ratio** — consistent with the
quadratic in declared-variable count that `lvar-lookup-cost-drivers.md` §5
measured (4.6² ≈ 21). So `|Σ|` is the multiplier on carrying cost, exactly as
§2d/§2f modelled before §3's earlier revision talked me out of it.

The rig is therefore usable for MECHANISM and useless for MAGNITUDE: its
K-coefficient is the coefficient at `|Σ|`=7, and real targets run at 32+.

> **RETRACTED 2026-09-07 — both halves.** See
> `table-entry-sigma-axis.md`, a 5×3 `|Σ|`×K grid with three held-out points.
> (1) The per-entry law is **LINEAR** in `|Σ|` — `3.0261 + 0.08188·D` M words,
> held out to 0.003% — and the total's quadratic coefficient is *independent of
> table size* to 0.006%, so the quadratic is not a table cost at all. A linear
> law cannot yield 28× from a 4.6× ratio, so the gap was never evidence of an
> exponent. (2) The two rigs are not comparable on this axis: `ZZPadShrCommon.v`
> has a CONCRETE base and empty `Σ0`, so after `peval` its table keys are bare
> `term_val`s with **no variable to look up**. It measures the residue; muladd
> measures residue + lookup. `|Σ|`=7 vs 32 was the wrong difference to read.
>
> The correct statement: 68–84% of the per-entry cost is the `env.lookup` walk
> inside `persist_itableW`, and the pad rig cannot see it.

### 3c. Two fixes, both now justified (the first LANDED — see 3d)

- **`is_exit` short-circuit (executor, small).  LANDED 2026-09-07, see 3d --
  and it turned out to also delete a per-step dead branch, so it is worth
  ~1.21x on every program on top of removing the overshoot.** `sexec_cfg_addr` builds BOTH
  sides of `angelic_binary (exit-branch) (execute-branch)` even when
  `is_exit apc` is already `true`, in which case the left side is `pure apc`, an
  unconditional success, and the right side is waste. Collapsing the choice when
  the pc is a declared exit removes regime 1 — **8% here**, and more for a
  segment leaving more fuel unspent. NOTE this is **not** a solver failure: the
  solver refutes one side of every demonic fork (`#block = #dbin + 1` exactly,
  both arms).
- **base+offsets (representation, a project).** §2j/§3 of earlier revisions
  describe it: one base term + one wide word term + a world-independent
  `list (N * AnnotInstr)`, making `persist_itableW` and `itableW_free` O(1) in K
  and `lookup_instr` one `peval` plus a numeric lookup. It attacks regime 2, i.e.
  **~797 M of `ZZSeg2P`'s 1232 M (~2.8× on that arm)**, and it makes table size
  free — which would remove the need for sub-table trimming rather than
  complementing it. Cost is reworking `itable_rel`, the `TablesRel.v` faith
  lemmas, and `wtable_rel`/`itable_relW_zip`.

Before funding base+offsets, isolate the `|Σ|` axis properly (§3b is a two-rig
fit). The cheap version: raise `|Σ|` on the pad rig at fixed table, fixed steps,
fixed chunks, and check the K-coefficient scales quadratically.

## 3d. FIXED 2026-09-07: the exit overshoot is gone, and so is a dead branch

`sexec_cfg_addr` no longer has an `angelic_binary` at all:

```coq
| S n' => if andb (negb first) (is_exit exits apc) then pure apc else (execute…)
```

`first` is set by `sexec_triple_addr` and cleared on every recursive call.

**Two effects, measured separately (matched same-session A/B).**

(1) The old exit ARM WAS DEAD on every non-exit step — it was `emsg`, so the old
form emitted an `angelic_binary` plus a dead `error` per step of every program.
Node census confirms exactly that: `ZZSegTrimP` goes `abin`/`error` 388/388 →
**372/372**, i.e. 16 pairs for ~16 executed steps, while `dbin`/`block` stay
438/439 (instruction-semantics forks, untouched). Worth a uniform **~1.21×** on
the pad rig:

| P | 0 | 16 | 32 | 64 | 128 |
|---|---:|---:|---:|---:|---:|
| before | 6.721 | 7.228 | 7.805 | 9.188 | 12.883 |
| after | 5.588 | 5.967 | 6.414 | 7.529 | 10.659 |
| ratio | 1.203 | 1.211 | 1.217 | 1.220 | 1.209 |

(2) **The fuel-dependent exit overshoot is eliminated.** Re-running §3's sweep:

| K | 15 | 16 | 18 | 20 | 25 | 35 | 75 |
|---|---:|---:|---:|---:|---:|---:|---:|
| marginal BEFORE | — | 10.209 | 14.288 | 17.685 | 3.033 | 3.040 | 3.049 |
| marginal AFTER | — | **3.012** | **3.023** | **3.011** | **3.017** | **3.021** | **3.030** |

Flat at 3.011–3.030 M/entry across the whole range, including the first entry
past the exit. The discontinuity that grew with every unit of slack fuel is
gone. On the arms: `ZZSeg2P` 1232.250 → **1164.651 M** (−67.6 M, 91% of the
74.2 M §3 attributed to overshoot); `ZZSegTrimP` 339.348 → 339.316 M
(**unchanged**, correctly — its table holds no instruction at the exit address,
so it never overshot). Per-entry 3.344 → 3.091 M/entry.

**`first` is NOT removable.** A loop-body segment contract starts and ends at the
SAME address (`exits_of_offs <base> [0]` against `asn_init_pc <base>` in
`PaddedLoop.v`, `CountdownComposed.v`, `TwoLoopsComposed.v`), so its trace visits
that address twice — execute at step 0, stop at step 2 — and the pc is the same
TERM both times. Fuel cannot substitute: the executor sees only what remains,
never the initial value. Dropping `first` and stopping at any declared exit was
tried and makes `pbody 0` fail with residual `v = v + 0xffffffff`, i.e. the
postcondition demanded at the entry.

What the old `angelic_binary` was really doing was two jobs at once: deciding
"am I done" (the exit table's job) and disambiguating the two visits (nothing
else can). Because it was a CHOICE it had to construct both branches, and that
construction is the fuel cost. `first` separates the jobs so "am I done" becomes
a decision.

**Proof side.** Only the symbolic executor changed; `cexec_cfg_addr` keeps its
unconditional `angelic_binary` (deliberately breaking cfgver-refinement's
"mirror the choice" rule), which is sound because `is_exit_sound` runs one way
only. `rexFS` went 4 cases → 3 and 270 → 198 lines: the exit-hit/exit-miss pair
merges, which deleted a verbatim 58-line copy of the core case that `rprop_or`
had glued on. New helpers `rprop_left`/`rprop_right` replace `rprop_or`.

**`./scripts/gate.sh` PASSED** — build clean, no holes, 18 end theorems
axiom-clean (only `Machine.pure_decode` / `Base.mmioenv`).

## 4. Files

Nothing was landed in the executor. The `peval apc` hoist of §1b was implemented,
measured at 0.0–0.1% (§2), and **reverted** — it buys nothing and `lookup_instr`
is pattern-matched in `VerifierRel.v`, so keeping a `let` there would have needed
a full gate run for no payoff. The word-column ablation of §2h was unsound by
construction and reverted the same way.

Rigs and probes (all `Example/`, throwaway, not in `_CoqProject`):

| file | role |
|---|---|
| `ZZPadCommon.v` + `ZZM_b{0,16,32,64,128}.v` | the K axis at constant steps (`pbody`), from `prefix-length-cost.md` |
| `ZZF_p{0,64}n{4,16}.v` | NEW — the `pflat` 2×2 that splits per-step from one-off (§2c) |
| `ZZSeg{2P,TrimP,Trim}.v` + `ZZSegBase.v` | muladd cut @220, the `PLAN-muladd-full.md` 2×2 |
| `ZZLvarInstrCommon.v` + `ZZSig_{pad,mul2P,mulTrimP}.v` | NEW wrappers — `zz_stats_raw` structural counts (§2e) |
| `ZZNodeKinds.v` + `ZZNK_{pad,mul2P,mulTrimP}.v` | NEW — per-constructor SymProp node breakdown, the probe that answered §3 |

Protocol: `OCAMLRUNPARAM='v=0x400'`, one heavy proof per `coqc`, `allocated_words`
net of an imports-only baseline re-measured per side, strictly serial, `Error`
gate on every arm. `ZZSegTrim` is the havoc'd arm and legitimately fails to close
(bare `False`, `PLAN-muladd-full.md`) — its allocation was read from the failure
log, as the earlier record did.
