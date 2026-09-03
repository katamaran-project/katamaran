# Hunting `Base(K)` — three candidates eliminated, one new suspect

Status: **Diagnostic record, 2026-09-02. `Base(K)` is still UNIDENTIFIED.** This
file is the negative-results record for it: what it is *not*, each with a
measurement, plus the method lesson each elimination carries. `Base(K)` is the
name given in `theories/diagnostics/env-lookup-cost-drivers.md` §9 to the
K-dependent block that is **62 % of peak footprint** and was identified only by
elimination — not variables (linear, 5–11 MB each), not chunks (1.18 MB each),
not the `SymProp` skeleton (nodes ↑2.49× while footprint ↑6.19×, KB/node 32→80),
not term-variable density (`occ/nodes` flat).

## Scoreboard

| candidate | verdict | evidence |
|---|---|---|
| `AMessage` snapshots on every `assertk` | **REFUTED as a large block** | ablation: peak heap unmoved (but see §1's quantisation caveat — this bounds it well below 62 %, it does not measure it at zero), 1.7–2.1 % of allocation (§1) |
| `subst (wco w) sub_wk1` — copying the path condition per extension | **REFUTED** | Σ\|wco\| at binders grows 1.438× where cost grows 2.283×; mean \|wco\| is ~10 formulas (§2) |
| `sub_wk1` construction | **not it, but real**: 3.9 % and *rising* (exponent 4.18 vs 3.44) — the only candidate here whose share grows (§3) |
| term SIZE in formula and vareq payloads | **REFUTED** | 72,099 term nodes in the whole tree at K=206; the ENTIRE tree is ≤2.6 % of peak (§4) |
| heap `persist` (chunk carrying) | **12.7 % of level, 9.6 % of GROWTH**, exactly linear in chunks — held-out +0.0017 % at both K (§5, §6). Not the quadratic. |
| `combined_solver` (construction-time) | **24.5 % of level, 22.8 % of GROWTH** — largest single mechanism found (§7). **LOAD-BEARING: halving its passes costs 20–25 % MORE (§8)** — it buys back more than it costs. Do not shorten it. Still not the scaling driver: exponent 3.08 vs total 3.44. |
| **transient construction state** (CPS closures, intermediate executor states, allocation churn) | **OPEN — 60.8 % of the GROWTH, exponent 3.96 vs total 3.44** (§4, §6, §7) |

# Part I — `AMessage` snapshots are NOT `Base(K)` (refuted 2026-09-02)

## One-sentence finding

Every `assertk` carries an `AMessage` holding the whole path condition, local
store and symbolic heap, in ordinary non-debug runs — but ablating it away
changes peak heap by **0.00 %** (12,800 words in 415 million) and total
allocation by only **1.7–2.1 %**, so messages are **not** the dominant footprint
block, and the `Base(K)` question is still open.

## 1. Why it looked like the answer

`Base(K)` had been identified only by elimination (`env-lookup-cost-drivers.md`
§9): 62 % of footprint, not variables, not chunks, not the `SymProp` skeleton
(nodes ↑2.49× while footprint ↑6.19×, KB/node 32→80), not term-var density. The
instrument that ruled those out states its own scope limit as *"not `AMessage`
contents and not the symbolic heap"* — so messages were the one named thing left.

They are also built unconditionally. `Config`'s `config_debug_function` /
`config_debug_lemma` (`MicroSail/SymbolicExecutor.v:266`, both `false` by
default) gate `SymProp.debug` **nodes**, not this:

```coq
Definition assert_formula :                          (* Monads.v:1268, SHeapSpec *)
  ⊢ (SHeap -> AMessage) -> Formula -> SHeapSpec Unit :=
  fun w msg C Φ h => SPureSpec.assert_formula (msg h) C (...)
```

`(msg h)` is applied with no flag, and `consume`'s `asn.formula` case
(`Monads.v:1330`) supplies `{| pathcondition := wco _; heap := h; ... |}`. The
message then enters every node via `assert_pathcondition_without_solver'`
(`Propositions.v:313`) and is **deep-copied** once per eliminated variable by
`assert_triangular`'s `let msg' := subst msg ζ` (`Propositions.v:341`), where
`SubstMessage` does `subst δ`, `subst h`, `subst pc`.

And it is provably inert: `Obligation msg fml ι <-> instprop fml ι`
(`Propositions.v:485`) — the constructor ignores `msg` entirely.

## 2. The ablation

Two-arm A/B on one commit. The variant arm is a scratch **copy** (never the
working tree, per this skill's rule), patched at the choke point where a message
enters the tree rather than at the ~20 construction sites — so construction is
untouched and the single axis moved is *carrying and copying*:

```coq
SymProp.assert_triangular amsg.empty ν      (* was: msg  -- Monads.v:340 *)
SymProp.error amsg.empty                    (* was: msg *)
⟨ θ ⟩ _ <- assertSecLeak amsg.empty t ;;    (* was: a full snapshot -- Monads.v:577 *)
```

Full `theories/` + CFGVer light chain rebuild in the copy: 17m44s, exit 0,
**zero errors** — which is itself a result: `amsg.empty` typechecks throughout,
confirming from the build that nothing downstream depends on message content.

Protocol tag **ALLOC** + peak heap via OCaml's own `top_heap_words` (not OS RSS,
which this directory records as pointing the wrong way between variants).

## 3. Results

Net of each arm's own `ZZDSB` baseline. **Baselines agree to 0.050 % (alloc) and
0.003 % (peak)**, so the import closures cost the same and the ratios are clean.
Both arms report identical peak `|Σ|` (96 at K=162, 135 at K=206), so they
verify the same VC.

| K | metric | BASE net | ABLATED net | saved |
|---|---|---|---|---|
| 162 | allocated | 1,592,697,620 | 1,558,982,772 | 2.12 % |
| 162 | **peak heap** | 178,776,576 | 178,770,944 | **0.00 %** |
| 206 | allocated | 3,635,767,677 | 3,572,859,352 | 1.73 % |
| 206 | **peak heap** | 415,208,448 | 415,195,648 | **0.00 %** |

Peak heap: 3.322 GB → 3.322 GB at K=206.

The base arm reproduces `env-lookup-cost-drivers.md` §7.1 to five significant
figures (1.5927 / 3.6358 G), so this is the same rig those conclusions rest on.

## 4. Reading it

**The 2 % allocation saving is the `subst msg ζ` deep copies** — ~63 M words over
4,031 variable eliminations, ≈15.6k words per copy. The mechanism is real; it is
transient, so it costs throughput and nothing in peak heap.

**The 0.00 % footprint was predictable from the code and should not have needed
an experiment.** The message record holds `{| pathcondition := wco _; heap := h |}`
— it **aliases** structures the world and the executor state already retain.
Removing an alias frees nothing, because the referent stays live either way. A
pure-aliasing structure cannot be a footprint driver. This was noticed
mid-investigation (an earlier estimate of "≈720 KB per message × 2,460 messages"
was corrected on exactly these grounds) but the correction was not followed
through to its conclusion, and an 18-minute rebuild plus 20 minutes of
measurement was spent on a question that reading answers. **Generalisable rule:
before ablating X for FOOTPRINT, ask whether X owns its bytes or aliases them.
For a THROUGHPUT question the same structure can still matter — copying an alias
is real work — which is why the two metrics disagreed here by two orders of
magnitude.**

## 5. What this means

- **Messages are removed from the `Base(K)` candidate list.** Do not revisit.
- A 1.7–2.1 % throughput fix does exist here and is free of trusted-surface risk
  (`Obligation` ignores the message; the ablated arm builds with zero errors).
  Not worth landing on its own, and it would cost the `DebugCFGVerifierContract`
  diagnostics; note it if something else makes messages worth touching.
- **`Base(K)` is still unidentified**, and the elimination list is now one longer.
- **The surviving candidate is the path conditions the messages were aliasing.**
  `wsnoc w b = MkWorld (wctx w ▻ b) (subst (wco w) sub_wk1)` builds a **fresh
  copy** of the whole path condition at every world extension, not shared with
  the parent, and every tree node is indexed by such a world. That is per-node,
  retained, and invisible to the instrument — the same fingerprint. It is the
  *application* half of the weakening cost whose *construction* half is measured
  at 3.9 % and rising in Part III below.

## 6. Files / reproduction

```bash
OFF=<scratch>; tar -cf - --exclude=.git --exclude=_build --exclude='*.vo' . \
  | (cd $OFF && tar -xf -)
# apply the three amsg.empty edits to $OFF/theories/Symbolic/Monads.v
(cd $OFF && make -f Makefile.coq -j1 case_study/RiscvPmp/CFGVer/Example/Prelude.vo)
# then, per arm, one process per point:
OCAMLRUNPARAM='v=0x400' coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran case_study/RiscvPmp/CFGVer/Example/ZZDS206.v
```

Gate every point on the `Eval` result line being present and `Error` absent.
Note `ZZDS*.v` use a bare `Eval`, not `Time Eval`, so **"Finished transaction"
never appears** and is the wrong string to gate on — that produced a false alarm
here.

---

# Part II — the path-condition copy is NOT `Base(K)` (refuted 2026-09-02)

## One-sentence finding

Part I's refutation left the structures the messages were *aliasing* as the
natural next suspect — `wsnoc` builds a fresh copy of the whole path condition
at every world extension — but the path condition averages only **~10 formulas**,
and its integral grows **1.438×** where total cost grows **2.283×**, so its share
is *falling* and it cannot be a 62 % block.

## The mechanism

```coq
Definition wsnoc (w : World) (b : LVar ∷ Ty) : World :=      (* Worlds.v:88 *)
  @MkWorld (wctx w ▻ b) (subst (wco w) sub_wk1).
```

Not shared with the parent — a genuine fresh copy per extension, and every tree
node is indexed by such a world. Right fingerprint (per-node, retained,
invisible to the instrument), wrong magnitude.

## Measurement

`wco` is **not reachable from the tree** — `SymProp` is indexed by `LCtx`, not
`World` — so it is reconstructed top-down: `pc` grows by one at each
`assertk`/`assumek` ancestor, and is accumulated at each binder node. Probe
`Example/ZZPC<K>.v`, one `Eval` per process.

| K | Σ\|wco\| over binders | binders | mean \|wco\| | Σ\|wco\| weighted by `fml_lw` |
|---|---|---|---|---|
| 162 | 30,770 | 3,082 | 9.98 | 107,111 |
| 206 | 44,241 | 4,152 | 10.66 | 147,332 |

Growth 162→206: **1.438×**, against total cost **2.283×**.

## Reading it

~44k formula-copies over the whole K=206 run. Even at a generous 1,000 words per
formula copy that is ~44 M words against 3.64 G — about 1 %, and shrinking as a
fraction. Same shape as `ctx.fresh` in `ctx-fresh-cost.md`: a real mechanism, too
small to matter, share falling with K.

---

# Part III — `sub_wk1` is Θ(\|Σ\|²) per extension: 3.9 % and RISING

## One-sentence finding

Building the weakening substitution costs **≈14 words per (variable × its de
Bruijn index)**, i.e. **Θ(\|Σ\|²) per world extension** — because `ctx.in_at` is a
**unary** `nat` — which is **3.3–3.9 % of total cost**, and unlike every other
candidate in this file its share **rises** with K (exponent 4.18 against total
cost's 3.44).

## The mechanism

```coq
Definition sub_wk1 {Σ b} : Sub Σ (Σ ▻ b) :=                   (* Terms.v:785 *)
  env.tabulate (fun '(ς∷σ) ςIn => @term_var _ ς σ (ctx.in_succ ςIn)).

Definition in_succ {b Γ b'} (bIn : In b Γ) : In b (snoc Γ b') :=
  @MkIn _ (snoc Γ b') (S (in_at bIn)) (in_valid bIn).          (* Context.v:203 *)
```

De Bruijn indices count from the **innermost** binder (`lookup (snoc _ b) O = b`,
`Context.v:113`), so adding one binder renumbers every variable in scope. The
k-th variable's index is `S^k O` — O(k) words. Tabulating all \|Σ\| of them is
therefore Σk = Θ(\|Σ\|²). The `In` *proof* is not the problem: `nth_is` computes to
an equality, so `in_valid` is `eq_refl`-sized.

**This is the second consequence of the fact that killed the skew RAL in
`env-lookup-cost-drivers.md` GATE 0.** That record concluded unary indices make
*lookup* unavoidably linear. They also make the *weakening substitution
quadratic to write down*, and one is built at every extension.

## Measurement

Two measurements multiplied, no rebuild. Microbenchmark `Example/ZZWk1Bench<n>.v`
(2000 builds, net of `ZZWk1BenchB` at 610,306,286); traffic from a variant of the
`ZZLvarInstrCommon` instrument whose `lv_bind` accumulates `sg*sg` instead of
`sg` (`Example/ZZSigSqCommon.v` + `ZZSQ<K>.v`) — every other counter came back
byte-identical, confirming only the accumulator changed.

| \|Σ\| | net words | words/build | **words / (n(n−1)/2)** |
|---|---|---|---|
| 34 | 18,260,922 | 9,130 | 16.3 |
| 97 | 130,536,388 | 65,268 | 14.0 |
| 136 | 252,301,214 | 126,151 | 13.7 |

The last column is flat — that is the Θ(n²) law, ≈14 words per (variable × index).

| K | extensions | Σ\|Σ\| | Σ\|Σ\|² | `sub_wk1` build | total | share |
|---|---|---|---|---|---|---|
| 162 | 3,082 | 137,914 | 7,575,890 | 52.1 M | 1.593 G | **3.27 %** |
| 206 | 4,152 | 255,568 | 20,687,322 | 143.0 M | 3.636 G | **3.93 %** |

Doubled if `acc_snoc_right` (`Worlds.v:345`) builds it a second time: 6.5–7.9 %.

## Reading it

Exponent in K is **4.18** against total cost's **3.44** — the only candidate in
this file whose share grows. But the gap is only 0.75, so it extrapolates to ~5 %
(or ~10 % doubled) at full length K=292, and would need K≈6000 to become half the
cost. **A fix to this alone buys at most ~1.09× at the scale that matters.**

It is nonetheless the most interesting structural finding here, because the fix
is not a micro-optimisation: making weakening free requires a
**weakening-stable variable representation** (de Bruijn *levels*, so `sub_wk1`
becomes `sub_id` and `subst (wco w) sub_wk1` becomes `wco w`). Katamaran is
**intrinsically scoped** — `Term Σ σ` carries `ctx.In` proofs — so making that
definitionally free reaches `Context.v`, `Environment.v`, `Worlds.v`, all of
`Symbolic/`, and the `Pred`/modality layer. Research-scale, and on these numbers
**not justified by `Base(K)`**, because `sub_wk1` is not `Base(K)`.

---

# Part IV — the tree is not the footprint, so `Base(K)` is not in it

## One-sentence finding

The **entire** finished VC — 36,970 `SymProp` nodes plus 72,099 term
constructor nodes — is at most **2.6 %** of the 3.32 GB net peak heap at K=206,
so `Base(K)` is not a retained structure in the tree at all, and every
tree-reachable candidate is thereby excluded at once.

## The measurement that opened it

The existing instrument never measured term SIZE. `tm_occ` counts only
`term_var`: `term_val` scores 0, and `term_binop`/`term_unop` add nothing for
themselves, so a term of 10,000 operator nodes over constants scores **zero**.
Every "the tree is small" reading taken from it was about *variable density*, not
bytes. `Example/ZZTN<K>.v` adds `tm_nodes`/`fml_nodes`/`sp_termnodes`, counting
every constructor:

| K | term nodes | `SymProp` nodes | growth of term nodes |
|---|---|---|---|
| 162 | 47,226 | 26,653 | — |
| 206 | 72,099 | 36,970 | 1.527× (vs total cost 2.283×) |

## Reading it

109,069 objects total at K=206. Against a net peak of 415,208,448 words
(3.32 GB):

| assumed words/object | tree total | share of peak |
|---|---|---|
| 20 | 17.5 MB | 0.53 % |
| 50 | 43.6 MB | 1.31 % |
| 100 | 87.3 MB | 2.63 % |

**So the finished VC is ~1–3 % of peak footprint.** Whatever holds the other
97 % is *not reachable from the `SymProp`* — which is precisely why four
successive tree-based instruments found nothing: they were all measuring an
object that is not the cost.

What is left, none of it tree-reachable: the CPS continuation closures
`sexec_cfg_addr` builds at every step (each capturing a world, a heap and a
store), the intermediate symbolic heaps threaded through execution, and garbage
the major GC has not reclaimed at the high-water mark.

**Method consequence, and the reason this file exists.** Four candidates were
eliminated one at a time, at a cost including one 18-minute full rebuild, when a
single structural question — *can the object I am dissecting even hold 3.32 GB?*
— excludes all four in one measurement. **Bound the container before dissecting
the contents.** The arithmetic needed was one term-node count.

## A near-proportionality that must NOT be quoted as a law

Across this sweep, peak heap tracks allocation closely:

| K | net alloc | net peak | peak/alloc |
|---|---|---|---|
| 162 | 1.5927 G | 178,776,576 | 0.11225 |
| 206 | 3.6358 G | 415,208,448 | 0.11420 |

Net peak grew 2.322× where net alloc grew 2.283× — within 1.7 %. It is tempting
to conclude footprint is simply ~11.4 % of allocation and there is no separate
footprint driver. **Do not.** `footprint-vs-throughput.md` measured the
`drop_fuel` axis at **10.5× throughput for 1.12× footprint** (that
throughput figure is SUPERSEDED 2026-09-03 — it was the `var_dead` scan bug,
now 22.7× cheaper and a net *win*; see `dropk-firing-payoff.md` ADDENDUM) — a 10×
decoupling. The two metrics genuinely separate on that axis. The constant ratio
here is an artifact of the K axis, along which every contributor scales
together; it is not a law and does not transfer.

## Correction to Part I

Part I reported the message ablation as **0.00 %** of peak heap. That figure
leans on `top_heap_words` at a ~2 % effect size, which is exactly the trap this
skill's checklist names: *"quantized to OCaml's ~15 % growth steps … produced a
confident 'this variant is free at every N' for a variant whose allocation
demonstrably grew 3×."* The two arms' peaks differ by 12,800 words — the
signature of both landing on the same heap-growth step, not of a measured zero.

**What the ablation does establish:** messages are not a *large* footprint block,
since a 62 % reduction would cross many quantisation steps. **What it does not
establish:** that they are exactly zero. The allocation figures (1.7–2.1 %) are
unaffected and stand. Part IV makes the point moot — nothing in the tree is
`Base(K)` — but the reasoning error should not be reused.

## What to do next

`Base(K)` needs an instrument that can see **live heap during construction**, not
the finished term: OCaml-level heap profiling (`Gc.stat` sampling, or a
`memtrace`/`statmemprof` run over one `ZZDS<K>` build) to attribute the
high-water mark to allocation sites. No Coq-level traversal can answer it, and
four have now tried.

---

# Part V — heap `persist` is 12.7 % and LINEAR; the weakening rewrite is not justified

## One-sentence finding

Carrying one heap chunk costs **15.38 M words, exactly linear** (held-out
**+0.0017 %**), so at the ~30 declared chunks of the muladd contract heap
`persist` is **12.7 %** of total cost — which, with `sub_wk1` (3.93 %) and the
path-condition copy (1.21 %), puts **everything attributable to eager weakening
at 17.8 %, an Amdahl ceiling of 1.22×** — and that does **not** justify a
weakening-stable-representation rewrite.

## Why this measurement

`lvar-lookup-cost-drivers.md` §5.2 established the mechanism — a chunk costs
16.1× more when its variables sit 64 binders deeper, "because `persist`
re-looks-up every occurrence at every world extension" — and concluded *"reduce
the DEPTH, not the chunk count."* That is the strongest statement in the record
that weakening is the `|Σ|²` driver. But it is from the ZZLvD rig, and this
skill is explicit that **magnitudes do not transfer between rigs**. The Amdahl
number for the muladd rig had never been taken.

## The experiment

**Axis: heap chunk count, at fixed `|Σ|` and fixed step count.** `PVConst`
(pinned constant) cells add a chunk but mint **no logic variable**, which is what
keeps this single-axis — the catalog records a previous chunk measurement
invalidated by exactly the confound of growing chunks and variables together.
Padding sits at addresses 828–1080: above the 206 instructions (which end at 824),
below the real data at 1128, under the existing 1168 bound, so nothing else in
the contract shifts. Probes `Example/ZZHP{0,16,32,64}.v`.

**Single-axis proof:** every arm prints its own peak `|Σ|`, and all four read
**135** with `err=0`. Had any read differently the comparison would be void.

## Results

| pad chunks | allocated | marginal words/chunk |
|---|---|---|
| 0 | 4,292,457,760 | — |
| 16 | 4,538,560,185 | 15,381,402 |
| 32 | 4,784,580,256 | 15,376,254 |
| 64 | 5,276,862,216 | 15,383,811 |

Constant to four significant figures. Fitting on {0, 64} and predicting the
withheld 32: **+0.0017 %**. Exactly linear — corroborating
`check-scalar-combined-cost-drivers.md` §6.6 on an independent rig.

Net cost at K=206 (no pad, baseline 656,591,136) = 3.6359 G words.
Heap carrying at ~30 declared chunks (20 register + 10 memory) = 0.461 G =
**12.7 %**.

Note `ptsto_instrs` lives in the Iris/soundness layer, not the symbolic VC, and
the per-fetch `encodes_instr` chunks are reclaimed by the 2026-08-03 chunk-GC —
so the live symbolic heap really is ~30 chunks, not one per instruction.

## Cumulative attribution at K=206

| mechanism | share | where measured |
|---|---|---|
| `ctx.fresh` | 0.39 % | `ctx-fresh-cost.md` |
| `sub_wk1` construction | 3.93 % | Part III |
| path-condition copy | 1.21 % | Part II |
| `AMessage` copies | 1.73 % | Part I |
| heap carrying, 30 chunks | 12.69 % | Part V |
| **identified** | **19.95 %** | |
| **UNIDENTIFIED** | **80.05 %** | |

## What this means

- **Do not fund the weakening rewrite on these numbers.** Eager weakening totals
  17.8 % (`sub_wk1` + pc copy + heap carrying) — ceiling **1.22×** — against a
  change reaching `Context.v`, `Environment.v`, `Worlds.v`, all of `Symbolic/`
  and the `Pred`/modality layer. The mechanism is real and the diagnosis was
  right; the prize is too small. This is the `select_last_k` lesson again:
  a correct diagnosis does not imply a fix worth building.
- **The `|Σ|²` driver is still unlocated, and 80 % of cost is unattributed.**
  Five Coq-level instruments have now each returned a single-digit or low-teens
  percentage. Combined with Part IV (the whole finished VC is ≤2.6 % of peak
  heap), the consistent reading is that the cost lives in **transient
  construction machinery** — CPS continuation closures, intermediate executor
  states, allocation churn — none of which any `Fixpoint` over `SymProp` can see.
- **Next instrument must be OCaml-level**, not Coq-level: `memtrace`/
  `statmemprof` over one `ZZDS<K>` build, attributing allocation to source
  sites. Every remaining Coq-side hypothesis is a guess until that exists.

## `top_heap_words` is unusable at this scale — confirmed hard

All four arms reported **byte-identical** `top_heap_words` (969,552,896) while
allocation grew **22.9 %**. That is a clean demonstration of the quantisation
caveat in this skill's checklist, and it independently justifies Part IV's
correction to Part I: no footprint conclusion in this file should rest on
`top_heap_words` differences, in either direction.

## Reproduction

```bash
# ZZHP<N>.v = ZZDS206.v with N pinned PVConst cells appended to mem_specs_rel.
# NOTE: an empty list must be written `@nil mem_spec_rel` -- a bare `[]` is
# hijacked by the ctx notations and yields "illegal begin of vernac".
for f in ZZHP0 ZZHP16 ZZHP32 ZZHP64; do
  OCAMLRUNPARAM='v=0x400' coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
    -R theories Katamaran case_study/RiscvPmp/CFGVer/Example/$f.v
done
```

Gate every arm on its printed peak `|Σ|` being 135 and `Error` absent — a failing
arm reports near-baseline allocation, which reads as "free" (it happened twice
while building these probes).

---

# Part VI — attribute the GROWTH, not the level: 83.6 % unidentified, and it grows FASTEST

## One-sentence finding

Decomposing the **increment** K=162→206 rather than the level: the identified
mechanisms account for only **16.4 % of the growth**, the unidentified remainder
grows at **2.418×** against total cost's **2.283×** (exponent **3.67** vs
**3.44**) — i.e. *faster* than the thing it is part of — so the quadratic lives
entirely in what no instrument here can see, and every mechanism named in this
file except `sub_wk1` is **diluting** the growth rather than driving it.

## Why the level table was the wrong table

Parts I–V each reported a mechanism's share of **total cost at K=206**. That
answers "how big is it", not "does it drive the scaling". A mechanism that is
12.7 % of cost but linear in K contributes nothing to the exponent; one that is
4 % but grows as K⁴ could dominate it. **For a scaling question the denominator
must be the increment.** Recorded because this file spent five parts on the
wrong denominator before the distinction was drawn.

## The missing measurement

Part V measured the per-chunk slope only at K=206, which cannot give a growth
contribution. Repeating the chunk-count axis at K=162 (`Example/ZZHQ{32,64}.v`;
pad-0 is `ZZDS162`, all arms printed peak `|Σ|` = 96, `err=0`):

| K | slope | held-out at 32 chunks |
|---|---|---|
| 162 | 8,839,835 words/chunk | **+0.0017 %** |
| 206 | 15,381,320 words/chunk | **+0.0017 %** |

Two independently fitted lines, same precision. Per-chunk cost grows **1.740×**
while K grows 1.272× — **exponent 2.31**. So carrying a chunk is exactly linear
*in chunks* but grows superlinearly *in K*, as expected: more steps means more
world extensions to persist through.

## The growth decomposition

Increment K=162→206 = 2,043,169,004 words (total 2.283×).

| mechanism | growth × | % of GROWTH | (cf. % of level) |
|---|---|---|---|
| `ctx.fresh` | 1.853 | 0.26 % | 0.39 % |
| `sub_wk1` construction | 2.747 | 4.45 % | 3.93 % |
| path-condition copy (est) | 1.438 | 0.66 % | 1.21 % |
| `AMessage` copies | 1.866 | 1.43 % | 1.73 % |
| heap carrying (30 chunks) | 1.740 | 9.60 % | 12.69 % |
| **IDENTIFIED** | | **16.41 %** | 19.95 % |
| **UNIDENTIFIED** | **2.418** | **83.59 %** | 80.05 % |
| *total* | *2.283* | | |

`AMessage` is the one row measured as a genuine two-arm difference at both ends
(BASE − ABLATED); `ctx.fresh`, `sub_wk1` and heap carrying are microbenchmark ×
traffic; the path-condition row multiplies a counted formula tally by an
**assumed** 1,000 words per copy, so its 0.66 % is order-of-magnitude only (its
1.438× growth ratio is solid, being a counted quantity).

## Reading it

- **The unidentified block grows faster than total cost** — 2.418× against
  2.283×, exponent 3.67 against 3.44. It is not merely the largest term; it is
  the only one accelerating.
- **Every identified mechanism except `sub_wk1` grows slower than total**, so
  they are *dilutants*: as K rises their shares fall. Cataloguing more mechanisms
  of this kind cannot converge on the driver.
- **`sub_wk1` is the sole mechanism outrunning total cost** (2.747× vs 2.283×)
  and is still only 4.45 % of the growth.
- **Eager weakening totals 14.72 % of the growth** (`sub_wk1` + pc copy + heap
  carrying), against 17.8 % of the level. The Part V recommendation stands and
  strengthens: **do not fund the weakening rewrite.**

## What this changes about next steps

Nothing about the direction — the next instrument still has to be OCaml-level
(`memtrace`/`statmemprof` over one `ZZDS<K>` build) — but it sharpens the target.
The profiler should be run at **two** K values and the allocation sites ranked by
**Δ between them**, not by absolute share. Ranking by absolute share is what this
file did for five parts, and it surfaces exactly the mechanisms that turn out not
to matter.

---

# Part VII — `combined_solver` is 24.5 % of cost / 22.8 % of growth

## One-sentence finding

`combined_solver` runs during **VC construction** (not `solve_vc`) and costs
**424,964,133 words at K=162 and 891,153,245 at K=206** — **24.5 % of the level
and 22.8 % of the growth**, by far the largest single mechanism identified — but
it grows at **2.097×** against total cost's 2.283× (exponent 3.08 vs 3.44), so it
too is a *dilutant* and not the scaling driver.

## It runs in `vm_compute`, not `solve_vc`

Two independent confirmations, worth stating because the answer decides whether
the ZZDS rig (raw construction, no `Qed`, no `solve_vc`) can see it at all:

1. `combined_solver` is called only at `Monads.v:337` and `:360`, inside
   `assert_pathcondition` / `assume_pathcondition`, and the `match` on its result
   **decides which `SymProp` constructor is emitted** (`assert_triangular ν …`
   vs `error`). The tree cannot be built without running it.
2. Empirically: the raw-tree instrument counts **4,031 `vareq` nodes** at K=206
   on `zz_vc_raw`, *pre-`postprocess`*. Those nodes are precisely the solver's
   triangular substitution entries.

## Why AMPLIFICATION and not ablation

The obvious experiment — stub `combined_solver` — is **confounded and would have
been uninterpretable**. The solver is what eliminates variables (peak `|Σ|` = 135
is the *post*-elimination figure; `lvar-lookup-cost-drivers.md` reports 1281 of
1293 mints eliminated on its rig). Stub it and no elimination happens, `|Σ|`
explodes, and the "ablated" arm can come out *slower*. Two axes move at once.

So the arm runs the solver **twice** and uses the second result:

```coq
match (match combined_solver w C with
       | Some _ => combined_solver w C
       | None   => combined_solver w C
       end) with
```

Scrutinising the first call makes it undeletable by the VM; both branches return
a second call, so the **value is identical** (pure function). Δ between arms is
exactly one solver pass, single-axis by construction.

**Both validity checks were stated before the run and both passed:** peak `|Σ|`
came back 96 / 135 (output unchanged, `err=0`), and cost went **up** — so the VM
did not share the duplicate calls. Had Δ been ≈0 the test would have been
*inconclusive*, not "the solver is free": a shared call and a free call are
indistinguishable in this metric.

## Results

Baselines 656,591,136 (base) vs 656,272,880 (amplified) — **0.048 % apart**.

| K | base net | amplified net | one solver pass | % of level |
|---|---|---|---|---|
| 162 | 1,592,697,620 | 2,017,661,753 | 424,964,133 | 26.68 % |
| 206 | 3,635,767,677 | 4,526,920,922 | 891,153,245 | 24.51 % |

Growth 2.097× against total 2.283× → **22.82 % of the increment**.

## Full attribution

| mechanism | growth × | % level | % GROWTH |
|---|---|---|---|
| `combined_solver` | 2.097 | 24.51 % | 22.82 % |
| heap carrying (30 chunks) | 1.740 | 12.69 % | 9.61 % |
| `sub_wk1` construction | 2.747 | 3.93 % | 4.45 % |
| `AMessage` copies | 1.866 | 1.73 % | 1.43 % |
| path-condition copy (est) | 1.438 | 1.22 % | 0.66 % |
| `ctx.fresh` | 1.853 | 0.32 % | 0.26 % |
| **IDENTIFIED** | | **44.41 %** | **39.23 %** |
| **UNIDENTIFIED** | **2.593** | **55.59 %** | **60.77 %** |

Exponents in K: total **3.44**, solver **3.08**, unidentified **3.96**.

**Additivity caveat:** these terms may not be cleanly additive. The solver
internally performs substitutions and lookups, and adding pinned chunks generates
formulas the solver then processes, so some double-counting between the solver
row and the heap/`sub_wk1` rows is likely. Treat 44.41 % as an upper bound on
what is explained.

## What this means

- **A quarter of construction cost is in one function**, and unlike everything
  else in this file the fix is ordinary Rocq work with no representation change
  and no TCB implication:

  ```coq
  Definition combined_solver : Solver :=                 (* Solver.v:3819 *)
    let g   := solver_generic in
    let gg  := solver_compose g g in
    let ggu := solver_compose gg solver in
    solver_compose ggu (solver_compose ggu gg).
  ```

  Five composed passes, with `solver_generic` appearing six times. **The obvious
  next experiment is to measure each composition layer's marginal value** — same
  amplification trick, or simply shortening the composition and checking the VC
  is unchanged. If any layer is idempotent on this workload it is a direct win on
  24.5 % of cost.
- **It is still not the scaling driver.** Exponent 3.08 vs total 3.44.
- **The residual now grows at exponent 3.96.** Every mechanism identified across
  Parts I–VII except `sub_wk1` grows *slower* than total cost, so peeling them off
  makes the unexplained remainder accelerate. 60.8 % of the growth remains
  unattributed and is the only thing outrunning the average by a wide margin.

## Reproduction

Scratch copy, both `combined_solver` call sites amplified as above, full
`theories/` + light chain rebuild (16m57s), then `ZZDSB`/`ZZDS162`/`ZZDS206` one
process per point. Gate on peak `|Σ|` = 96/135 and `err=0`.

---

# Part VIII — the solver is LOAD-BEARING: halving its passes costs 20–25 % MORE

## One-sentence finding

Cutting `combined_solver` from 8 passes to 4 leaves **1,182 more undischarged
asserts (+48 %)** and makes total cost **1.249× at K=162 / 1.204× at K=206** —
so the solver's 24.5 % (Part VII) is buying back *more* than it costs, and the
"shorten the composition" hypothesis is **refuted**.

## The hypothesis and why it was wrong

Part VII observed that `combined_solver` is eight passes (`g g u g g u g g`) and
suggested the later ones might be redundant. `core-executor-internals` already
warned against this — *"an un-discharged assert permanently enlarges `wco` with a
redundant copy, and every later `wco` walk pays for it — a term-size-independent
quadratic if it happens per step"* — and that warning was recorded as a risk but
the shortening was still proposed as the likely win. It is not.

## The experiment

Scratch arm with `combined_solver := ggu` (4 passes: `g g u`) instead of
`solver_compose ggu (solver_compose ggu gg)` (8). Full rebuild 17m05s, exit 0.
**`combined_solver_spec`'s proof — `auto using solver_compose_spec,
solver_generic_spec, solver_spec` — went through unchanged**, which is the
soundness-by-construction property exercised rather than argued: any composition
of spec-satisfying solvers satisfies the spec. Shortening risks *completeness*,
never soundness.

Baselines 0.049 % apart.

## Results

| counter (K=206) | 8-pass | 4-pass | |
|---|---|---|---|
| `lv_binders` / `lv_vareqs` | 4,152 / 4,031 | 4,152 / 4,031 | same |
| `lv_maxsig` / `lv_sigint` | 135 / 255,568 | 135 / 255,568 | same |
| `lv_lw` / `lv_occ` | 85,061 / 2,196 | 85,061 / 2,196 | same |
| term nodes | 72,099 | 72,099 | same |
| `lv_nodes` | 36,970 | 38,978 | **+2,008 (+5.4 %)** |
| **`sp_asserts`** | **2,460** | **3,642** | **+1,182 (+48.0 %)** |

| K | 8-pass net | 4-pass net | ratio |
|---|---|---|---|
| 162 | 1,592,697,620 | 1,988,713,189 | **1.249×** |
| 206 | 3,635,767,677 | 4,378,677,690 | **1.204×** |

## Reading it

Every variable- and term-related counter is **byte-identical**: the shorter
solver mints the same variables, eliminates the same variables, and produces the
same terms. The *sole* structural difference is undischarged asserts. So passes
5–8 exist to discharge 1,182 asserts — 48 % of the total — and the cost of *not*
doing so exceeds the cost of the four passes, via the `wco`-growth feedback loop:
each surviving assert is appended to `wco` (`wpathcondition`, `Worlds.v:104`), and
stage 2 of `solver_generic` (`assumption_pathcondition (wco w0) C1`) walks `wco`
on **every subsequent solver call**.

This is the first quantification of that documented mechanism.

Note the penalty *shrinks* with K (1.249× → 1.204×) and the 4-pass arm's growth
exponent is slightly lower (2.202× vs 2.283× over this interval). Two points
only; do not read a law into it.

## What this means

- **`combined_solver` is not over-provisioned. Do not shorten it.**
- Its Part VII cost of 24.5 % of level / 22.8 % of growth is a *net* figure that
  already includes the saving it generates elsewhere; the gross saving is larger.
- **Optimising the solver means making each pass cheaper, not running fewer.**
  The remaining lever from Part VII — fixpoint-detecting early exit in
  `solver_compose` — is still sound *and* complete by construction (skipping a
  pass that provably computes its own input changes nothing), but its ceiling is
  lower than Part VII implied, because passes demonstrably do work.
- **Open, and the cheap next experiment: is 8 the optimum, or just where someone
  stopped?** The loop is hand-unrolled with no saturation test. A 12-pass arm is
  a one-line change with no soundness risk. If `sp_asserts` falls below 2,460 and
  cost falls with it, that is a free win on a quarter of construction cost.

## Reproduction

`combined_solver := ggu` in `theories/Symbolic/Solver.v:3819` in a scratch copy;
rebuild `theories/` + light chain; compare `ZZDSI206` (LvStats), `ZZAST206`
(`sp_asserts`), `ZZTN206` (term nodes) against base before comparing cost — a
moved VC makes the cost figure incomparable.

---

# READ BEFORE THE LOOP-INVARIANT WORK (written 2026-09-03)

This file is the cost-model record the invariant discussion will reach for, so
the four things that discussion needs are stated here rather than left implicit.

**1. Two numbers in this directory are RETRACTED as laws.** The CFGVer total
"exponent 3.44" and the derived `footprint ~ K^2.22 * |Sigma|^0.83` fit. A
four-point sweep at CONSTANT `|Sigma|` = 33 (`dropk-firing-payoff.md` ADDENDUM
PART 2) shows marginal cost over equal-width 22-instruction windows swinging
**649 -> 297 -> 548 M words** -- the muladd prefix is structurally
heterogeneous, so any two-point exponent measures point selection. **Quote a
marginal cost: 22.6 M words/instruction at `|Sigma|`=33 (range 13.5-29.5).**
Minimum four points before fitting an exponent on this rig. This file's own
"exponent in K" columns inherit the caveat; its SHARE columns (solver 22.8% of
growth, etc.) are ratios at fixed endpoints and survive.

**2. `Base(K)` is the wall, and no lever in this directory touches it.**
`mlen=2` dies on MEMORY. `Base(K)` -- footprint minus the `|Sigma|` term, i.e.
instructions plus the live tree -- is **62% of peak footprint and rising**
(`footprint-vs-throughput.md` §2.4, at `drop_fuel=0`; **unmeasured at fuel 8**).
Classing, pinning, sharing, byte blocks, word slicing, chunk-GC, the
`env.lookup` rewrite and dropk are ALL `|Sigma|` or constant-factor levers.
This is what invariants would actually attack.

**3. Decide `drop_fuel` first — the gate at fuel 8 has never been run.** At
fuel 8 the drop pins peak `|Sigma|` at 33 regardless of program length, and
since the `var_dead` fix that is free: 1.87x throughput and 2.66x footprint at
K=206, both GROWING with K. That removes the `|Sigma|` axis outright and leaves
program length as the sole target -- which sharpens the invariant case, but
moves the baseline invariants would improve on. It changes every VC, so it needs
its own gate run (`GATE_JOBS=1`, ~40 min).

**4. Compare the cheaper alternative before committing.** Whether the VC must be
built whole before `solve_vc` consumes it (`footprint-vs-throughput.md` §3's own
unattempted suggestion). Fusing construction and consumption, or discharging and
freeing subtrees, attacks `Base(K)` **without touching the executor's cost law
and without requiring users to write relational two-run invariants** -- the
latter being a change to what CFGVer *is*, from automatic/bounded to annotated.
