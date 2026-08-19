# PLAN — is logical-variable *lookup* the driver? (Dominique's hypothesis)

Status: **DONE 2026-08-19 — results in `diagnostics/lvar-lookup-cost-drivers.md`.**
Headline: chunk count spawns ZERO variables and costs a flat 1.289 M words each,
but the SAME chunk costs 16.1× more when its variables sit 64 binders deeper, so
the two are one multiplicative term rather than competing drivers. Pure lookup
depth at identical `|Σ|` is 1.16×–1.47×; declared-variable count is quadratic
(held-out +0.17% at 4× beyond the fit range). **One labelling error in this plan
is corrected there**: the `pad ∗ real` arm is not a pure breadth arm, because the
contract's own `"a"` variable precedes the pads in both arms.

Everything below is the plan **as committed before any measurement**, kept
unedited so the design can be audited against the results. Written first on
purpose: every retracted figure in `diagnostics/` was a comparison-design error,
not noise (the metric's own repeat error is 0.0008%), and the cheapest guard is
to write down what each variant is allowed to move before the numbers exist.

## The question

`diagnostics/check-scalar-combined-cost-drivers.md` §6.6 and
`diagnostics/key-schedule-loop2-cost-drivers.md` both concluded that the
logic-variable **count** `|Σ|` is the quadratic factor and chunk count `H` is
exactly linear. Neither says *which mechanism* consumes the `|Σ|`. Dominique's
hypothesis is that it is the **lookup** of logical variables. The classed-builder
re-measurement leaves a residual at exponent ≈1.22 and rising, explicitly
**unidentified**, and this plan is the sweep that record says was never run.

Second question, from Emiel: does the machinery **spawn** variables in proportion
to chunk count? If so, "chunk count" and "`|Σ|`" were never separable axes and
both prior records are reading one coupled term.

## Five mechanisms, not one

Grounded in code, because "variable lookup" is not a single cost:

| id | mechanism | code | scales with |
|---|---|---|---|
| **L1** | **lookup depth.** `env.lookup` walks a de Bruijn index; index = *number of binders introduced after* that variable, so a variable's index GROWS as Σ grows. | `Environment.v:153`, `Context.v:194–205` | (occurrences) × (depth) |
| **L2** | **substitution breadth.** `sub_wk1`/`sub_id`/`sub_shift` are `env.tabulate` over the whole Σ, rebuilt at every world extension whether or not anything is used. | `Terms.v:771–801` | (extensions) × \|Σ\| |
| **L3** | **transport volume.** `persist a ω = subst a (sub_acc ω)` walks all of `a`. Applied to the heap (H×T) per step — *and* `wsnoc w b := MkWorld (Σ ▻ b) (subst (wco w) sub_wk1)` re-substitutes the **entire path condition** at every fresh variable. | `Worlds.v:89`, `Worlds.v:515` | H·T·depth **+ \|pc\|·depth** |
| **L4** | bare count `\|Σ\|` — what the prior records measured. A *proxy* for L1/L2/L3/L5. | — | — |
| **L5** | **fresh-name generation.** `ctx.fresh` builds `names xs` (a list of all \|Σ\| names) and `List.find`s it on **every mint**; on a base-name collision it then runs `max_with_base` — a second full scan with `split_at_dot` string parsing per element. Per-step mints always collide (`"a"`, `"np"`, `"na"`), so they always take the expensive branch. | `Context.v:707–714`, `Monads.v:298–310` | (mints) × \|Σ\| × string work |

L1 alone predicts the observed quadratic: a spec variable declared up front is
looked up at step *S* at depth ∝ *S*, once per occurrence per persist. So does
L5, by a completely different route and with zero chunks involved. L2/L3/L5 are
**breadth** costs (they care how long Σ is); L1 is a **depth** cost (it cares
where in Σ the *used* variables sit). Nothing measured so far separates them,
and they have different fixes:

- L1 dominant → declaration ORDER is a free lever; hot variables belong innermost.
- L2 dominant → represent weakening as an O(1) coercion instead of a tabulated `Sub`.
- L3-pc dominant → stop re-substituting the path condition at every `wsnoc`.
- L5 dominant → name variables by a counter. **Cheapest fix of the five, and it
  changes no statement, no spec and no proof.**

## Axes

| axis | states | moved by |
|---|---|---|
| `chunks` | 0 \| 32 \| 64 (pad words × 4) | `pw` on the ZZPadShr rig |
| `sigma-len` | base \| base+K | K dead `asn.exist`s |
| `hot-depth` | base \| base+K | **position** of those pads: produced FIRST (real vars keep baseline depth) vs LAST (real vars +K deeper) |
| `steps` | constant everywhere | concrete base, `n = 4` fixed |

`sigma-len` and `hot-depth` are **separate axes** and that separation is the whole
point of the design. `produce (a1 ∗ a2)` produces left-then-right and the world is
threaded monadically (`Monads.v:1020`), and a de Bruijn index counts binders added
*after* the variable (`Context.v:201`), therefore:

- `pad ∗ real` → pads deep, **real vars at baseline depth**. Moves `sigma-len` only.
- `real ∗ pad` → pads shallow, **real vars +K deeper**. Moves both.

so `(real∗pad) − (pad∗real)` = **pure L1**, and `(pad∗real) − (pad0)` = **pure
L2+L3+L5**. Both arms have identical `|Σ|`, identical chunk count, identical step
count, identical instruction sequence, identical formulas, identical term shapes,
and an identical number of world extensions. The only difference is the integer
in each variable leaf.

### Variant table

Rig: `ZZPadShrCommon.v` arm B (concrete base, `n=4`, `S` constant, pad cells share
one variable so the pre-existing `|Σ|` axis is pinned). Pads: `dead_exists K`, K
existentials with no chunk and no occurrence.

| variant | pads | chunks | \|Σ\| | hot-depth | file |
|---|---|---|---|---|---|
| `pw{0,8,16}-K0` | none | 0/32/64 | base | base | `ZZPadShrB_PW{0,8,16}.v` (existing) |
| `pw{0,8,16}-K64-first` | `pad ∗ real` | 0/32/64 | +64 | base | `ZZLvarDepthCommon.v` + `ZZLvF_PW*_K64.v` |
| `pw{0,8,16}-K64-last` | `real ∗ pad` | 0/32/64 | +64 | **+64** | `ZZLvarDepthCommon.v` + `ZZLvL_PW*_K64.v` |
| `pw8-K64-split` | 32 first + 32 last | 32 | +64 | +32 | `ZZLvS_PW8_K64.v` |

`split` is the held-out linearity check: if cost is linear in hot-depth it must
land halfway between `first` and `last` at the same pw.

### Readings this grid licenses

1. **L1 (depth)** = `last − first`, at each pw. Divided by K = cost per depth-unit.
2. **L2+L3+L5 (breadth)** = `first − K0`, at each pw.
3. **Interaction chunks × depth** = does `last − first` grow with pw? L3's heap
   term (H·T·depth) says yes and proportionally; L5 and L3-pc say no.
   - grows with pw ⇒ chunks and lookup are ONE bilinear term, not two drivers.
   - flat in pw ⇒ the depth cost is chunk-independent (L3-pc / L1-on-pc), and
     cutting chunks does nothing for it.
4. **Linearity in depth** = `split` vs the midpoint of `first`/`last`.

### Known imperfection, stated rather than smoothed over

`real ∗ pad` mints its K pads when the precondition's path condition is already
built, `pad ∗ real` mints them when it is empty. Via L3-pc that adds
K × |pc_pre| re-substitution to the `last` arm on top of the depth effect. Bound:
execution performs ≥3 mints per step over S steps, so K pad-mints are ≈ K/(3S) of
all mint events and at a *smaller* pc than average — at `n=4`, S ≈ 52,
so ≈ 64/156 ≈ 40% of events but at the smallest pc in the run. This inflates the
L1 reading; it does **not** flip the chunks-vs-variables conclusion, because both
components are variable-machinery costs and neither involves H. Quantified against
the instrument's `sigint`, not assumed away.

## Experiment A — the instrument (structural, not a cost difference)

Stop inferring `|Σ|` and count it. `SymProp.Statistics` (`Propositions.v:1018`)
has `size`/`count_nodes` but no binder count. `ZZLvarInstrCommon.v` adds, over the
**raw** (pre-`postprocess`) VC:

| statistic | what it answers |
|---|---|
| `binders` (`angelicv`+`demonicv`) | how many variables the executor minted |
| `vareqs` (`assert_vareq`+`assume_vareq`) | how many the solver eliminated |
| `maxsig` (max `ctx_len Σ` over nodes) | peak `\|Σ\|` |
| `sigint` (Σ of `ctx_len Σ` over binder nodes) | the L2/L5 integral — total tabulate/name-scan work |
| `lw` (Σ of `ctx.in_at` over every `term_var` occurrence) | the L1 integral — total `env.lookup` work |
| `nodes` | `SymProp` size, for normalisation |

Run over `ZZPadShrB_PW{0,4,8,16}` (chunks 0→64 at `|Σ|` pinned):

- `binders` flat in pw ⇒ chunk count does **not** spawn variables. Emiel's worry
  closed by direct measurement rather than by a code reading.
- `binders` rising in pw ⇒ confirmed, and `lw` prices it on the spot.

Prediction from the code (recorded so it can be wrong): **flat**.
`consume_chunk` is a scan plus one `assert_pathcondition` (`Monads.v:828`);
`consume_chunk_angelic`'s `angelic_list (heap_extractions h)` branches H ways but
binds nothing (`Monads.v:855`); the mint sites are `call_contract`'s
`angelic_ctx id Σe` + `demonic result` (`Monads.v:1091,1102`) and `produce`/
`consume` of `asn.exist` (`Monads.v:1026,1073`) — all per *call*, never per chunk.

Also run over `ZZKslCLS_N{4,8,16}` to get the growth of `lw` and `sigint` with N
on the rig whose exponent-1.22 residual is the open question. Combined with
Experiment B's cost-per-depth-unit this gives a **fit-free closure test**: does
(cost per depth-unit) × `lw` account for the residual, or only a fraction of it?

Design risk: `postprocess` prunes, so counts on the postprocessed VC are a lower
bound on binders actually created. Measured on the raw VC for that reason; a
`_post` runner reports both where it matters.

## Protocol

`allocated_words` via `OCAMLRUNPARAM='v=0x400'`, one heavy computation per `coqc`
process, gate on `Finished transaction`, subtract an imports-only baseline
**re-measured on today's commit** (it moved +39% in six days). Arms generated from
one another by `sed` so only the intended token can differ. **Every results table
carries a protocol column** — a `Qed`/`Admitted` mismatch is worth 1.81×, which
exceeds the largest genuine effect in this directory. Protocol here is uniformly
`intros. Time vm_compute. Time solve_vc. Admitted.`, copied verbatim from
`ZZPadShrB_PW8.v`.

## Before proposing any fix (the three questions this project keeps forgetting)

To be answered in the diagnostic, not here:

1. Predicted end-to-end speedup at the N we care about (N=32/64), from the fit.
2. Constant factor or exponent change? In those words.
3. Is the mechanism still dominant after the fix? If L1 is 30% of cost, the
   ceiling is 1.43× and the other 70% is the new wall.

## Output

`diagnostics/lvar-lookup-cost-drivers.md`. Throwaway probes:
`Example/ZZLvarInstrCommon.v`, `Example/ZZLvarDepthCommon.v`,
`Example/ZZLv{F,L,S}_PW*_K*.v`, `Example/ZZLvI_*.v`, baselines
`Example/ZZLvBase.v`, `Example/ZZLvIBase.v`. None in `_CoqProject`.
