# Logical-variable lookup vs chunk count — which is the driver?

Status: **Diagnostic record, 2026-08-19.** Designed against
`plans/PLAN-lvar-lookup.md`, whose axes were committed to disk before any
measurement. Prompted by Dominique's hypothesis that the way logical variables
are *looked up* is a main driver, and by the question of whether some internal
process spawns variables in proportion to chunk count.

## One-sentence finding

**Chunk count spawns exactly zero logical variables and costs a flat 1.29 M
words each to carry, but a chunk whose variables sit 64 binders deeper costs
16.1× more — so chunk count is not an independent driver, it is a multiplier on
logical-variable lookup, and lookup depth at *identical* `|Σ|` is worth
1.16×–1.47× on its own while declared-variable *count* enters quadratically
(held-out +0.17% at 4× beyond the fit range).**

## 0. Protocol

Two protocols, never mixed, both recorded per table because a protocol mismatch
is worth 1.81× in this directory:

| tag | protocol | what it yields |
|---|---|---|
| **COST** | `intros. Time vm_compute. Time solve_vc. Admitted.` — copied verbatim from `ZZPadShrB_PW8.v` | `allocated_words`, gated on `finished=2/2` |
| **INSTR** | `Time Eval vm_compute in (zz_stats_raw …)` on the **raw** (pre-`postprocess`) VC | structural counts, gated on `finished=1/1` |

`OCAMLRUNPARAM='v=0x400'`, one heavy computation per `coqc` process, run
sequentially. Baselines re-measured on this commit (893e5b92):

| baseline | imports | `allocated_words` |
|---|---|---|
| `ZZLvDBase` | depth rig (COST) | **604,337,349** |
| `ZZLvIBasePS` / `ZZLvIBaseCLS` / `ZZLvIBaseD` | + instrument (INSTR) | 639,713,822 / 639,705,741 / 639,733,652 |

`ZZLvDBase` lands 0.009% from the published 604,283,692, and the K0 arm
reproduces `ZZPadShrB_PW0`'s published net (0.4055 G) to four digits, so this rig
is the published rig. Repeat error measured incidentally: the pw=0 INSTR point
run twice gave 958,264,732 and 958,267,712 — **0.0003%**.

## 1. The instrument (Experiment A)

`SymProp.Statistics` (`Propositions.v:1018`) counts nodes but no binders, and
nothing anywhere measured lookup depth. `Example/ZZLvarInstrCommon.v` adds seven
counts over the raw VC:

| statistic | meaning | mechanism it prices |
|---|---|---|
| `binders` | `angelicv` + `demonicv` | how many variables were minted |
| `vareqs` | `assert_vareq` + `assume_vareq` | how many the solver eliminated |
| `maxsig` | max `ctx_len Σ` over nodes | peak `\|Σ\|` |
| `sigint` | Σ of `ctx_len Σ` over **binder** nodes | L2 `env.tabulate` + L5 `ctx.fresh` scan, per mint |
| `lw` | Σ of `ctx.in_at` over every `term_var` | **L1: total `env.lookup` walk length** |
| `occ` | `term_var` occurrences | so `lw/occ` = mean depth |
| `nodes` | `SymProp` size | normalisation |

**Scope limit, stated because it explains a result below:** only formula and
`vareq` payloads are weighed, not `AMessage` contents. The symbolic **heap** is
therefore *not* counted, so `lw` excludes every occurrence living in a chunk.
`lw` is a lower bound, and specifically a *pc-and-store-only* bound.

## 2. Chunk count spawns no variables (Experiment A, part 1)

Rig `ZZPadShrCommon.v` arm B: concrete base, `n=4` (so steps constant), pad cells
sharing one existential (so `|Σ|` pinned), `pw` pad words = `4·pw` chunks.

| pw | chunks | binders | vareqs | maxsig | sigint | lw | occ | nodes | COST net |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 0 | 1293 | 1281 | 25 | 26524 | 3387 | 874 | 10722 | 0.40553 G |
| 4 | 16 | 1293 | 1281 | 25 | 26524 | 3387 | 874 | 10722 | — |
| 8 | 32 | 1293 | 1281 | 25 | 26524 | 3387 | 874 | 10722 | 0.44677 G |
| 16 | 64 | 1293 | 1281 | 25 | 26524 | 3387 | 874 | 10722 | 0.48802 G |

*(INSTR nets 0.31855/0.33909/0.35962/0.40068 G, marginal 5.135/5.133/5.133 M per
pad word — the COST column's marginal is 5.1561/5.1559 M, matching §6.6's
published 5.1554/5.1551 across a protocol change.)*

**Every structural count is byte-identical across a 4× range of chunk count.**
Not approximately — identically. The code says why: `consume_chunk` is a scan
plus one `assert_pathcondition` (`Monads.v:828`), `consume_chunk_angelic`'s
`angelic_list (heap_extractions h)` branches `H` ways but binds nothing
(`Monads.v:855`), and the mint sites are `call_contract`'s `angelic_ctx id Σe`
plus `demonic result` (`Monads.v:1091,1102`) and `produce`/`consume` of
`asn.exist` (`Monads.v:1026,1073`) — all per *call*, never per chunk.

**So the hypothesis that chunk count drives variable creation is refuted
structurally, not statistically.** Chunk count is a pure carrying cost of
**1.289 M words per chunk**, exactly linear.

### The other half of that table: `|Σ|` does not accumulate

Peak `|Σ|` is **25** while 1293 variables are minted and **1281 are eliminated**.
Per-step variables *churn*; they do not pile up. Consequence for reading the
prior records: the "`|Σ|` is quadratic" result cannot be about per-step
variables — it is about **declared** `PVExist` entries specifically, which
nothing constrains and therefore nothing eliminates. That is a sharper statement
than either prior record makes, and it is why §5 below finds the quadratic using
dead existentials that are never referenced at all.

It also names a mechanism the plan missed: **1281 variable *eliminations*, each a
triangular substitution over the whole path condition and heap.**

## 3. On the KSL classed rig, nothing variable-related is superlinear

Same instrument, `ZZKslClassCommon.v` — the rig whose exponent-≈1.22 residual
`key-schedule-loop2-cost-drivers.md` leaves explicitly unidentified. `ia` is
unused by the symbolic VC (`Contracts.v:119`) so a literal 256 is faithful.

| N | binders | vareqs | maxsig | sigint | lw | occ | nodes | INSTR net |
|---|---|---|---|---|---|---|---|---|
| 4 | 1281 | 1261 | **24** | 26230 | 7814 | 663 | 9115 | 0.35362 G |
| 8 | 2541 | 2521 | **24** | 52254 | 15582 | 1323 | 18203 | 0.76546 G |
| 16 | 5061 | 5041 | **24** | 104302 | 31118 | 2643 | 36379 | 1.78459 G |

Every count is exactly linear in N — binders `+315` per trip flat, `sigint`
×1.9922/×1.9961, `lw` ×1.994/×1.997, `nodes` ×1.997/×1.998 — and peak `|Σ|` is
**24 at every N** (the classed builder working as designed). Yet cost grows
×2.165 then ×2.331, i.e. **exponent 1.114 then 1.221**, reproducing that record's
published CLS exponents (1.114, 1.220) to three digits on a different protocol.

**So the unidentified residual there is not variable count, not lookup depth, not
mint count and not output size.** It is superlinear work over a linear-sized
object. Both chunk count and step count grow linearly with N on that rig, so
their product is quadratic; a mostly-linear cost plus a modest bilinear
`chunks × steps` term is consistent with 1.22. This record **rules variables out**
and does not identify what remains — that still needs the chunk-pinned /
step-pinned sweep that record asks for.

## 4. Lookup depth, isolated at identical `|Σ|` (Experiment B)

### The axis

A de Bruijn index counts binders introduced *after* a variable
(`ctx.in_zero = 0` for the innermost, `Context.v:201`) and `env.lookup` walks it
(`Environment.v:153`). `produce (a1 ∗ a2)` produces left-then-right with the
world threaded monadically (`Monads.v:1020`). So `K` dead existentials
(`dead_exists K`, no chunk, no occurrence, never referenced) placed *before* vs
*after* the real precondition give the same `|Σ|` and different indices.

| variant | pads | maxsig | sigint | occ | nodes | mean depth |
|---|---|---|---|---|---|---|
| `K0` | none | 25 | 26524 | 874 | 10722 | 3.9 |
| `F64` | `pad ∗ real` | **89** | 111292 | **874** | **10786** | 15.3 |
| `L64` | `real ∗ pad` | **89** | 111228 | **874** | **10786** | **67.2** |

`F64` and `L64` agree on `|Σ|` exactly, on `sigint` to 0.06%, and on occurrence
count and node count *exactly*. Chunks, steps, instructions, formulas and term
shapes are identical by construction. The only difference is the integer in each
variable leaf.

**Correction to the plan:** `F64` is *not* a pure breadth arm. The contract's own
`"a"` variable precedes the pads in both arms, so `F64` already carries a partial
depth increase (mean 3.9 → 15.3). `L64 − F64` is therefore the clean depth
reading; `F64 − K0` is breadth plus that partial depth. This gives two depth
levels at identical `|Σ|`, which is better than planned, but the plan's labelling
was wrong and is superseded here.

### Cost (COST protocol, net of 604,337,349), G words

| pw | chunks | `K0` | `F64` | `L64` | `L64/F64` |
|---|---|---|---|---|---|
| 0 | 0 | 0.405525 | 3.893303 | 4.520310 | **1.1610×** |
| 8 | 32 | 0.446774 | 3.934551 | 5.185393 | **1.3179×** |
| 16 | 64 | 0.488021 | 3.975807 | 5.850473 | **1.4715×** |

**Pure lookup depth, at identical `|Σ|` and identical everything else, is worth
1.16× to 1.47×.** Dominique's hypothesis is confirmed as a real, isolated
mechanism rather than a proxy for variable count.

Linearity in depth, held out: `S64` (32 pads first + 32 last, so the real
precondition is +32 rather than +64 deep) should land at the midpoint of `F64`
and `L64`. Predicted 4.559972, **measured 4.564656, +0.103%.**

## 5. Reading the axes apart

### 5.1 The depth surcharge is exactly linear in chunk count

`L64 − F64` = 0.627007 / 1.250842 / 1.874666 G at 0 / 32 / 64 chunks. Fit on the
first two, predict the third:

> depth surcharge = **0.627007 + 0.0194948 · chunks** G words
> predicted at 64 chunks 1.874676, actual 1.874666, **error −0.00053%**

Zero fitted parameters left over, five significant figures. So the depth cost
splits into a **chunk-independent** part (0.627 G — the path condition and store)
and a part **exactly proportional to chunk count** (the `persist` of heap chunks,
`Worlds.v:515`, each variable occurrence re-looked-up at every world extension).
This is why §2's `lw` did not move with chunk count: the instrument excludes
heap-resident occurrences.

### 5.2 A chunk costs 16.1× more when its variables are deeper

Marginal cost per pad word (4 chunks), same rig, same terms, same steps:

| arm | marginal per pad word | per chunk |
|---|---|---|
| `K0` (mean depth 3.9) | 5.1561 M | 1.289 M |
| `F64` (mean depth 15.3) | 5.156 M | 1.289 M |
| `L64` (mean depth 67.2) | **83.135 M** | **20.78 M** |

**16.1×, for the same chunk.** At 64 chunks the chunks' own carrying cost is
82 M words while their contribution to the depth penalty is 1.248 G — **15×
larger.** Chunks are cheap to carry and expensive to look through.

That is the answer to "separate chunk count from variable lookup": they are not
separable as competing drivers, because the dominant chunk-related cost *is* a
lookup cost. The chunk axis and the depth axis multiply, exactly and linearly.

### 5.3 Declared-variable count is quadratic — held out at 4× the fit range

Breadth curve, pads-first, pw=8 (`|Σ| = 25 + K`):

| K | \|Σ\| | COST net | marginal per pad |
|---|---|---|---|
| 0 | 25 | 0.446774 G | — |
| 16 | 41 | 0.966488 G | 0.03248 G |
| 32 | 57 | 1.722152 G | 0.04723 G |
| 64 | 89 | 3.934551 G | 0.06914 G |
| 128 | 153 | 11.192312 G | 0.11406 G |

Marginal cost per added variable rises linearly (×1.454, ×1.464), i.e. the total
is quadratic. Fit on K ∈ {0,16,32} only:

> cost(K) = **0.446774 + 0.0251087·K + 0.00046084·K²** G words

| held-out point | predicted | actual | error |
|---|---|---|---|
| K=64 | 3.941331 | 3.934551 | **+0.172%** |
| K=128 | 11.211088 | 11.192312 | **+0.168%** |

K=128 is four doublings beyond the fit range and lands inside 0.17%. This
independently reproduces §6.6's quadratic-in-`|Σ|` result (held-out +0.20%) on a
different rig, with a different mechanism for adding the variables — **dead
existentials that no chunk, formula or instruction ever references.** Declaring
them is the entire cost.

Restated as the comparison §6.6 makes: one declared logic variable versus one
declared chunk, using the fitted marginal —

| `\|Σ\|` | marginal per variable | per chunk | ratio |
|---|---|---|---|
| 25 | 25.1 M | 1.289 M | **19.5×** |
| 89 | 84.1 M | 1.289 M | **65×** |
| 153 | 143.1 M | 1.289 M | **111×** |

This explains the spread in the previously published "~30–46× one chunk": the
ratio is not a constant. Variable cost is quadratic, chunk cost is linear, so the
ratio grows linearly with `|Σ|`. **Never quote a single number for it without
saying at which `|Σ|`.**

### 5.4 Attribution of the K=64 surcharge

At pw=8, total surcharge over `K0` is 4.738619 G:

| component | G words | share | mechanism |
|---|---|---|---|
| breadth + `"a"`-depth (`F64 − K0`) | 3.487777 | 73.6% | L2 `env.tabulate` per mint (`Terms.v:785`), L5 `ctx.fresh`'s `List.find`/`max_with_base` over all `\|Σ\|` names (`Context.v:707`), L3 pc re-substitution at every `wsnoc` (`Worlds.v:89`) |
| pure depth of real precondition vars (`L64 − F64`) | 1.250842 | 26.4% | L1 `env.lookup` walk (`Environment.v:153`), of which 0.627 G chunk-independent and 0.624 G via heap `persist` |

`F64 − K0` is 3.487777 / 3.487777 / 3.487786 G at 0 / 32 / 64 chunks — **constant
to 0.0003%, entirely chunk-independent**, which is exactly what L2 and L5 predict
(they depend on `|Σ|` and mint count, never on the heap) and what L1-via-heap
does not.

Candidate for the quadratic specifically, from the code and not yet isolated:
`sub_comp ζ1 ζ2 = subst ζ1 ζ2` maps `subst` over an `Env` of `|Σ|` terms
(`SubstEnv`, `Terms.v:767`), each doing an `env.lookup` of depth up to `|Σ|` — so
**composing two substitutions is O(|Σ|²)**, and the executor composes one per
world extension. Per-mint `tabulate` and `ctx.fresh` are each O(`|Σ|`) with a
fixed mint count, which gives a *linear* term, not the quadratic. Isolating this
would need an ablation inside `Worlds.v`; not attempted here.

## 6. What this means

Ranked by what a fix would buy, with Amdahl applied — the step this project's
checklist says is routinely skipped.

1. **The cheapest real lever is declaration ORDER, and it is free.** Depth is
   worth 1.16×–1.47× at fixed `|Σ|`, and `S64` shows it is linear in how many
   binders sit after the hot variables. Anything that must be existential should
   be declared **as late as possible** (innermost), and per-step variables are
   already cheap because they are minted last. This changes no statement, no
   spec, no proof — only the order of conjuncts in a precondition. It is a
   **constant factor**, not an exponent change.
2. **Not declaring a variable at all remains worth far more**, and now has a
   sharper price: 19.5× a chunk at `|Σ|`=25, 111× at `|Σ|`=153. `PVConst` over
   `PVExist`, and the classed builders, stay the first thing to reach for. This
   is an **exponent** effect (quadratic → the term vanishes), which is why it is
   ranked here despite (1) being cheaper to apply.
3. **Chunk-side work is a dead end for a third time, but for a NEW reason.**
   Carrying a chunk is 1.289 M words, flat. The reason chunk count appears to
   matter is that each chunk multiplies the lookup-depth cost by 0.0195 G per
   64-deep shift. **Reduce the depth, not the chunk count** — the same 64 chunks
   cost 82 M or 1.33 G depending only on where their variables sit.
4. **L5 (`ctx.fresh`) is worth its own experiment and was not isolated here.**
   Every mint builds the full name list of `Σ` and `List.find`s it, then on a
   base-name collision runs `max_with_base` — a second full scan with
   `split_at_dot` string parsing per element (`Context.v:707–714`). Per-step
   mints always collide (`"a"`, `"np"`, `"na"`, `Verifier.v:188,501,507`), so they
   always take the expensive branch. It is inside the 73.6% breadth block above,
   undifferentiated from L2 and L3-pc. If it is a large share, the fix — name by
   a counter — is the cheapest in the whole catalog and changes nothing
   observable. **This is the recommended next experiment.**
5. **The KSL exponent-1.22 residual is still open**, but variables are now
   excluded from the suspect list (§3), which is a real narrowing: the remaining
   candidate is the bilinear `chunks × steps` carrying term, and §5.1 gives a
   calibrated per-chunk-per-depth coefficient to test it against.

## 7. Files and reproduction

Throwaway, none in `_CoqProject`:

| purpose | files |
|---|---|
| instrument | `Example/ZZLvarInstrCommon.v` |
| depth/chunk rig | `Example/ZZLvarDepthCommon.v` (extends `ZZPadShrCommon.v`) |
| COST grid | `Example/ZZLvD_PW{0,8,16}_{K0,F64,L64}.v`, `ZZLvD_PW8_S64.v` |
| breadth curve | `Example/ZZLvD_PW8_{F16,F32,F128}.v` |
| INSTR, chunk axis | `Example/ZZLvI_PS_PW{0,4,8,16}.v` |
| INSTR, KSL classed | `Example/ZZLvI_CLS_N{4,8,16}.v` |
| INSTR, depth self-check | `Example/ZZLvI_D_PW8_{K0,F64,L64}.v` |
| baselines | `Example/ZZLvDBase.v`, `ZZLvIBasePS.v`, `ZZLvIBaseCLS.v`, `ZZLvIBaseD.v` |

Rebuild the `Common` chain first — the pre-existing `.vo`s were stale against
today's `Prelude.vo` and fail with "makes inconsistent assumptions over library":

```
for f in ZZLvarInstrCommon ZZPadShrCommon ZZKslChunkDistinctCommon \
         ZZKslClassCommon ZZLvarDepthCommon; do
  coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
    case_study/RiscvPmp/CFGVer/Example/$f.v
done
```

then one process per point, sequentially:

```
OCAMLRUNPARAM='v=0x400' coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran case_study/RiscvPmp/CFGVer/Example/<Runner>.v 2>&1 \
  | grep -E 'allocated_words|Finished transaction|Error'
```

Gate on `finished=2/2` (COST) or `1/1` (INSTR) and `errors=0` before trusting a
number. Whole sweep is ~50 min on this box; `ZZLvD_PW8_F128` alone allocates
11.8 GB.

### Instrument notes for reuse

`env.snoc` takes its binding **explicitly** (`env.snoc E' _ db`, three pattern
arguments), `env.Env` needs `B : Set` not `Type`, and there is no `env` fold in
`Environment.v` — `env_sum` supplies one. A recursive call under `env_sum`'s
functional argument passes the guard checker for `Env`-of-`Term` arguments,
which is the same shape `sub_term` uses (`Terms.v:747`).
