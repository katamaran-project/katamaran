---
name: cfgver-refinement
description: >
  Katamaran CFGVer refinement layer — the concrete (shallow) executor cexec_cfg_addr
  that is refined by the symbolic term-table executor sexec_cfg_addr, the
  RefineCompat relation structure, and the rexec_cfg_addr relational-correctness
  lemma (under itable_rel/etable_rel table-faithfulness premises). Use when reading
  or extending the relational layer, proving a new relational (ℛ⟦⟧) lemma, or
  understanding why the concrete mirror exists at all. NOT for driving or debugging
  the rsolve tactic itself — failures, hangs, memory blowups, missing instances —
  that is cfgver-rsolve. NOT for the symbolic executor's own semantics
  (cfgver-executor).
---

# CFGVer refinement: the concrete mirror + relational correctness

Proof apparatus, not decision logic. `cexec_cfg_addr` is the concrete (shallow,
`CHeapSpec`) executor, still gmap-based (`instrs !! v`); `sexec_cfg_addr` is the
symbolic, term-table-based executor (**cfgver-executor**). The two dispatch
differently — gmap lookup on a concrete address vs. syntactic term matching modulo
`peval` — so the two executors are not a step-for-step mirror of each other. The
soundness argument still factors as

```
symbolic VC  --(refinement: rexec_cfg_addr, this skill)-->  concrete execution
             --(Iris soundness: cfgver-soundness)-------------->  myWP2_loop / leakage
```

## What cexec_cfg_addr and sexec_cfg_addr share — and where they diverge

`cexec_cfg_addr` (`VerifierRel.v`, Shallow section) and `sexec_cfg_addr`
(`Verifier.v`, Symbolic section — the two live in different files since the
2026-07-27 Iris split) share the outer shape but differ at the dispatch step:

| Decision point | `sexec_cfg_addr` (symbolic) | `cexec_cfg_addr` (concrete) |
|---|---|---|
| fuel | `match fuel` → `error` / step | identical |
| pc probe | none — dispatch tries the table match directly | `ty.RVToOption apc` — *do both worlds agree (SyncVal)?* is a real semantic gate, not just a mirrored probe |
| choice | `angelic_binary` exit / execute | identical |
| exit branch | `if is_exit exits apc then pure apc else error` (peval/`Term_eqb` table match) | `if exitCond v then pure apc else error` (direct bool call) |
| dispatch | `lookup_instr tbl apc` → `error` / **(word term, instruction)** (peval/`Term_eqb` table match) | `instrs !! v` → `error` / instruction (gmap lookup); the word comes from `words v` |
| step | `⟨θ1⟩ apc' <- sexec_instruction i apc anp wd ;; recurse`, persisting `tbl`/`exits` via `persist_itableW`/`persist_etable` | `apc' <- cexec_instruction i apc anp (SyncVal (words v)) ;; recurse` |

Both executors carry two extra arguments since 2026-07-31/08-01: `anp` (the
incoming nextpc, threaded rather than re-existentialised per step) and the raw
instruction WORD. The symbolic side reads the word out of its table's third
column; the concrete side applies `words : bv xlenbits -> bv word`, a TOTAL
function (not a gmap — that would add a "no word here" branch carrying no
information). See **cfgver-executor** for why the word must be supplied at all.

The concrete side's `ty.RVToOption apc` probe has **no explicit symbolic
counterpart** — it's not a mirrored decision point but a genuine requirement of the
two-world model (the pc must already agree across worlds to read one), which
`rexec_cfg_addr` discharges by case analysis inside the proof rather than by a
paired `refine_bind`. This is why `rexec_cfg_addr`'s proof is NOT written in
`rsolve` style (per its own TODO in `VerifierRel.v`) and is flagged as a golf target —
unlike a clean structural mirror, matching the two sides here needs explicit
`itable_rel`/`etable_rel` faithfulness facts (below), not just instance search.

**MIRROR (still mandatory where it applies):** fuel and the recursive step.
**NO LONGER the exit/execute choice, deliberately (2026-09-07):**
`sexec_cfg_addr` has no `angelic_binary` at all — it stops iff
`negb first && is_exit` — while `cexec_cfg_addr` keeps its unconditional
`angelic_binary`. That asymmetry is SOUND and is the whole point:
`is_exit_sound` runs one way only (`is_exit = true -> exitCond v = true`), so the
symbolic side may be strictly MORE decisive, which makes the VC stronger. The
payoff was removing a per-step dead branch (1.21× on every program) and a
fuel-dependent overshoot past mid-program exits; see **cfgver-executor** and
`diagnostics/table-entry-cost.md` §3d. Consequence for `rexFS`: the symbolic side
is always a SINGLE branch, so its cases take `rprop_left` / `rprop_right` into
the concrete disjunction rather than `rprop_or`. **DON'T MIRROR (symbolic-only bookkeeping):**
world-indexed binds (`⟨θ1⟩` substitutions), `persist_itable`/`persist_etable`
threading, path conditions, and error-message payloads (`amsg` with
`debug_string_pathcondition`; concrete errors are a bare `error`).

Above the executors sits `cexec_triple_addr` (demonic Σ/pc intro → ASSUME
`itable_faith`/`etable_faith` at the chosen valuation → `produce req` → run →
`consume ens`) — note the source comment: `run` performs **no leakcheck**. The
guard makes the triple hold vacuously except at the one valuation the end-to-end
proof discharges it at (`refine_guard`, `VerifierRel.v`).

## `RefineCompat` — the relation structure

Relational goals between symbolic and concrete programs are closed instance-by-
instance via the typeclass

```coq
Class RefineCompat (R : 𝕊 w -> C -> Prop) (c : C) (w : World) (s : 𝕊 w) ... :=
  MkRefineCompat { refine_compat : R s c }.
```

Key instances in `CFGVer/VerifierRel.v`: `refine_compat_angelic_binary` and
`refine_compat_cfg_verification_condition` (the full VC). The tactic that
drives the instance search is `rsolve` — using and debugging it effectively is the
**cfgver-rsolve** skill.

Don't confuse this `RefineCompat`/`ℛ⟦⟧` machinery (CFGVer's OWN
`sexec_cfg_addr`-vs-`cexec_cfg_addr` pair) with the SAME-LOOKING `refine_*`
lemma naming and `ℛ⟦⟧` notation one layer further down, in the CORE generic
`SPureSpec`-vs-`CPureSpec` monad every case study is built on
(`theories/Refinement/Monads.v`) — that's **core-executor-internals**, not
this skill.

## `rexec_cfg_addr`

The relational-correctness lemma refining `cexec_cfg_addr` by `sexec_cfg_addr`,
proved by `iInduction` on fuel, GIVEN `itable_relW instrs words tbl` and
`etable_rel exitCond exits`. **THREE subgoals since 2026-09-07** (was four): when the stop guard holds the
symbolic side is `pure ta` and `lookup_instr` is never consulted, so the old
exit-hit/exit-miss pair MERGES — which also deleted the old case 1, a verbatim
58-line copy of the core case that `rprop_or` had glued on (270 → 198 lines).
Goals are 1 = stop, 2 = run/lookup-hit, 3 = run/lookup-miss. They are discharged
sequentially by hand rather than through `rsolve`/`refine_bind` pairing — see the
divergence note above. **Keep the cases explicitly selected/bracketed**: the
script used to be positional, and when `sexec_cfg_addr` gained `anp` the first
case stopped closing, silently shifting every later block by one goal and
surfacing as an unresolvable evar nowhere near the cause.

**`itable_relW` vs `itable_rel` — the distinction to keep straight:**

- `itable_rel instrs tbl` is the Σ-level, WORD-FREE guard: every key term
  instantiates to a `SyncVal` address the gmap maps the same way. This is what
  `cexec_triple_addr` assumes, what `TablesRel.v`'s faith lemmas prove, and what
  `EndToEnd.v` discharges. **Unchanged by the word threading.**
- `itable_relW instrs words tbl` is the loop-carried relation over the fused
  `SInstrTableW`, adding `inst x ι = SyncVal (words v)` per entry. It is
  **DERIVED, not assumed**: `itable_relW_zip` builds it at the entry point from
  `itable_rel` plus `wtable_rel` plus the demonic words' refinement. Because the
  word rides in the same table entry as the address, the two gmap lookups are
  tied together and the concrete executor's word branch cannot diverge.

`wtable_rel` is boundary-only — consumed once by `itable_relW_zip`, never
threaded through the induction. That is the concrete payoff of fusing the word
into the table instead of keeping a parallel word table, which would have needed
its own persist/forgetting/lookup/faith family alongside `itable_rel`'s.

Prefer `itable_relW_zip_pred` (the Iris-level wrapper) over `iStopProof` at the
call site: `iStopProof` folds the WHOLE persistent context into one conjunction,
so its intro pattern breaks whenever an unrelated hypothesis appears earlier.

In its lookup-hit branches, `destruct (lookup_instr ... )`/`instrs !! v`-shaped
matches can silently fail to reduce and stall `refine_bind` — that's a generic
stdpp-gmap pitfall; see the **gmap-pitfalls** skill for the mechanism and fix.
