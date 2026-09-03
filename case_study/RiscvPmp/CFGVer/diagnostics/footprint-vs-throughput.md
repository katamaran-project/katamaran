# Footprint is not throughput — and they have different drivers

Status: **Diagnostic record, 2026-09-01.** Prompted by the `env.lookup` rewrite
(`theories/diagnostics/env-lookup-cost-drivers.md`), which cut *allocation* 2.9×
and *peak live heap* by exactly zero, and by the observation that this whole
directory is written in `allocated_words` and therefore **cannot, as written,
tell a throughput lever from a footprint lever**.

## One-sentence finding

Peak live heap obeys `Base(K) + ~5–11 MB per declared logic variable + 1.18 MB
per chunk`, in which **`|Σ|` enters LINEARLY** (not quadratically as it does for
throughput) and the **instruction/tree term `Base(K)` is 62–71% of the total** —
so the `mlen`=2 memory wall is driven by program length and the live `SymProp`
tree, and neither the `|Σ|` levers nor the chunk levers in this directory's
catalogue can move it.

## 0. Protocol

| tag | protocol |
|---|---|
| **FOOT** | `OCAMLRUNPARAM='v=0x400' /usr/bin/time -f "RSS %M"`, one heavy `Eval`/proof per process, reading **`top_heap_words` and peak RSS** alongside `allocated_words`, all net of an imports-only baseline |

`top_heap_words` proved **too coarse to use as the primary metric here**: it
moves in exact 1.15× steps (OCaml's heap-growth increment), so on the muladd rig
a 4.1× cut in `|Σ|` registered as *one step*, and on the `ZZLvD` rig it was
pinned at the floor for every chunk-axis arm. **Peak RSS is the working
footprint metric** in this record; `top_heap_words` is quoted only where it
independently agrees. This is the same low-end saturation
`cfgver-scaling-diagnostics` already warns about, met head-on.

Gate on `err=0` and (COST rig) `fin=2`. Two arms in this study initially
reported *baseline-level* footprint because they failed to compile — the
"this variant is free" failure mode — and were caught only by that gate.

## 1. Axes

| axis | states | rig that moves it ALONE |
|---|---|---|
| `chunks` | 0 / 32 / 64 | `ZZLvD_PW{0,8,16}_K0` — fixed `\|Σ\|`=25, fixed steps |
| `variables` | `\|Σ\|` 25 → 89 | `ZZLvD_PW8_{K0,F64}` — dead existentials, no chunk, no occurrence |
| `variables` (2nd rig) | `\|Σ\|` 135 → 33 | muladd `ZZDS{162,206}` at `drop_fuel` 0 vs 8, **fixed K** |
| `depth` | mean 15.3 vs 67.2 | `ZZLvD_PW8_{F64,L64}` — identical `\|Σ\|`, identical everything else |
| `instructions` | K = 140…206 | muladd `ZZDS<K>` prefix |

## 2. Results

### 2.1 Chunks, at fixed `|Σ|` and fixed steps — LINEAR, and cheap

| arm | chunks | net RSS | net alloc |
|---|---|---|---|
| `ZZLvD_PW0_K0` | 0 | 0.099 GB | 146.9 M |
| `ZZLvD_PW8_K0` | 32 | 0.136 GB | 175.5 M |
| `ZZLvD_PW16_K0` | 64 | 0.173 GB | 204.2 M |

Fit on the first two, predict the third: **181,056 KB predicted vs 180,932
actual, +0.07%.** So **1.18 MB of peak heap per chunk**, exactly linear.
(Allocation: 0.90 M words/chunk, consistent with this directory's published
1.289 M.)

### 2.2 Declared variables — LINEAR, 5–11 MB each, on two independent rigs

| rig | `\|Σ\|` moved | at | net RSS | MB per variable |
|---|---|---|---|---|
| `ZZLvD_PW8_K0`→`F64` | 25 → 89 | fixed chunks/steps | 0.136 → 0.774 GB | **10.80** |
| muladd `ZZDS162`, drop 0→8 | 96 → 33 | **fixed K** | 1.245 → 0.933 GB | **5.08** |
| muladd `ZZDS206`, drop 0→8 | 135 → 33 | **fixed K** | 2.876 → 2.045 GB | **8.34** |

**Linear, not quadratic.** Quote a range, not a number — the constant varies
5–11 MB across rigs, exactly as this directory already says about the analogous
throughput constant ("never quote a single number for it without saying at which
`|Σ|`").

### 2.3 Depth — a throughput axis, essentially NOT a footprint one

`F64` vs `L64`: identical `|Σ|`, identical chunks, identical node count; only the
de Bruijn indices differ.

| | alloc | net RSS |
|---|---|---|
| `ZZLvD_PW8_F64` | 1.750 G | 0.774 GB |
| `ZZLvD_PW8_L64` | 1.990 G | 0.784 GB |
| ratio | **1.137×** | **1.013×** |

Depth costs 14% of allocation and 1% of footprint. This is the cleanest
statement in the record of why the two metrics need separating.

### 2.4 The residual: instructions, and it dominates

Subtracting §2.2's per-variable term from the muladd points leaves an
`|Σ|`-independent base:

| K | net RSS | `\|Σ\|` term | **`Base(K)`** | Base as % of net |
|---|---|---|---|---|
| 162 | 1.245 GB | ~0.47 GB | **0.77 GB** | **62%** |
| 206 | 2.876 GB | ~1.10 GB | **1.78 GB** | **62%** |

Consistency check the model was not fitted to: the two `drop_fuel=8` arms have
`|Σ|`=33 at *both* K, so their footprint difference is almost pure `Base`:
0.933 → 2.045 GB over K 162→206. `Base` more than doubles for a 1.27× rise in K.

### 2.5 Why the tree skeleton is not the explanation either

Structural counts on the same muladd prefixes (`ZZLvarInstrCommon`, patched for
`dropk` — it predates that constructor and its four matches were non-exhaustive):

| K | nodes | occ | `\|Σ\|` | net RSS | **KB per node** |
|---|---|---|---|---|---|
| 140 | 14,869 | 863 | 42 | 0.454 GB | **32.0** |
| 206 | 36,970 | 2,196 | 135 | 2.812 GB | **79.8** |

Footprint grows 6.19× while nodes grow 2.49×, `occ` 2.54×, `sigint` 4.95×,
`lw` 4.58×. **Nothing tracks it**, and `occ/nodes` is flat (0.0580 → 0.0594), so
it is not term-variable density. The average node gets 2.5× heavier. Note the
instrument's own scope limit (`lvar-lookup-cost-drivers.md` §1): it weighs only
formula and `vareq` payloads, **not `AMessage` contents and not the symbolic
heap** — so the unexplained mass is, by construction, in the part it cannot see.

## 3. What this means

- **`|Σ|` is quadratic for throughput and LINEAR for footprint.** That single
  asymmetry explains why `drop_fuel` looks like a disaster on this directory's
  usual metric and does almost nothing for memory: at K=206 it pays **12.17×
  allocation** (see §4) to buy **1.41×** footprint.
- **The dominant footprint term is `Base(K)`** — instructions and the live tree
  — at 62% and rising. **`mlen`=2 needs that term reduced.** Neither classing,
  pinning, variable sharing, byte-granular blocks nor chunk GC touch it; they are
  all `|Σ|`/chunk levers, i.e. the 38%.
- **Levers whose whole value is trading allocation for a smaller live term have
  been systematically mis-scored** by every record in this directory, because
  the metric could not see the thing they buy.
- **Cheap and unattempted:** whether the VC must be built whole before
  `solve_vc` consumes it. If construction and consumption can be fused, or
  subtrees discharged and freed, `Base(K)` is attackable without touching the
  executor's cost law at all.

## 4. Side result: `var_dead`'s scan is not lookup-bound

Full 2×2 at K=206, net of baselines — the `env.lookup` rewrite × `drop_fuel`:

| | `drop_fuel=0` | `drop_fuel=8` | drop penalty |
|---|---|---|---|
| old `lookup` | 10.510 G | 45.319 G | **4.31×** |
| new fused walk | 3.636 G | 44.233 G | **12.17×** |

> **SUPERSEDED 2026-09-03 for the `drop_fuel=8` COLUMN — the 12.17× and 4.31×
> are measuring a cost bug in `var_dead`'s scan, not the drop mechanism.**
> `var_dead` was an eight-conjunct `&&`, and `&&` is `andb`, a function, so
> call-by-value evaluated every conjunct — including a full `occurs_check`
> REBUILD of the O(K) instruction table — for every candidate variable at every
> step. Short-circuiting it and moving the table last takes `drop_fuel=8` from
> 44.233 G to **1.947 G (22.72×)**, at which point the drop is **1.87× cheaper
> than `drop_fuel=0`**. The `drop_fuel=0` column and every conclusion in §2/§3
> are unaffected (the drop is `pure tt` there, so `var_dead` never runs — the
> 3.636 G reproduces to +0.0111% post-fix). Full record and control:
> `dropk-firing-payoff.md`, ADDENDUM 2026-09-03. Do not requote 12.17× or the
> "pays 12.17× allocation to buy 1.41× footprint" line below as a property of
> dropk.
| lookup win | **2.891×** | **1.025×** | |

The rewrite is worth 2.89× to the executor and **1.02× to `var_dead`'s scan** —
so that scan is traversal over path condition, heap, `trans`, `apc`, `anp`,
table and exits, not `env.lookup` walking. It also **confirms
`muladd-full-cost-drivers.md` §3.5's 4.30× drop penalty at 4.31× on a properly
matched pair**, retiring that figure's standing caveat ("the fuel-8 arm reuses
the fuel-0 import baseline… not re-measured here").

## 5. Files / reproduction

Throwaway, gitignored, none in `_CoqProject`:

| purpose | files |
|---|---|
| chunk + variable + depth axes | `Example/ZZLvD_PW{0,8,16}_K0.v`, `ZZLvD_PW8_{F64,L64}.v`, baseline `ZZLvDBase.v` |
| instruction axis + `drop_fuel` | `Example/ZZDS{140,162,184,206}.v`, baseline `ZZDSB.v` |
| structural counts | `Example/ZZDSI<K>.v` + `ZZLvarInstrCommon.v` |

```bash
OCAMLRUNPARAM='v=0x400' /usr/bin/time -f "RSS %M WALL %e" \
  coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
  case_study/RiscvPmp/CFGVer/Example/<probe>.v 2>&1 \
  | grep -E 'allocated_words|top_heap_words|RSS|Finished|Error'
```

Two traps hit here, both costing a full sweep:

- **The `Common` chain's `.vo`s go stale** against a rebuilt `Prelude.vo` and
  fail with *"makes inconsistent assumptions over library"*. Rebuild
  `ZZByteLoop2Common` → `ZZPadShrCommon` → `ZZLvarDepthCommon` in that order
  first. The failed arms reported **baseline-level** footprint, i.e. read as
  "free".
- **`ZZLvarInstrCommon.v` predates `SymProp.dropk`** and has four
  non-exhaustive matches (`sp_stats`, `sp_asserts`, `sp_assumes`, `sp_branch`).
  Patched 2026-09-01.
- **`drop_fuel` lives in `Verifier.v:934`**, so an arm needs only the CFGVer
  light chain rebuilt in a scratch copy — `theories/` is shared and untouched.
