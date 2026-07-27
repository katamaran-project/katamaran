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
| dispatch | `lookup_instr tbl apc` → `error` / instruction (peval/`Term_eqb` table match) | `instrs !! v` → `error` / instruction (gmap lookup) |
| step | `⟨θ1⟩ apc' <- sexec_instruction i apc ;; recurse`, persisting `tbl`/`exits` via `persist_itable`/`persist_etable` | `apc' <- cexec_instruction i apc ;; recurse` |

The concrete side's `ty.RVToOption apc` probe has **no explicit symbolic
counterpart** — it's not a mirrored decision point but a genuine requirement of the
two-world model (the pc must already agree across worlds to read one), which
`rexec_cfg_addr` discharges by case analysis inside the proof rather than by a
paired `refine_bind`. This is why `rexec_cfg_addr`'s proof is NOT written in
`rsolve` style (per its own TODO in `VerifierRel.v`) and is flagged as a golf target —
unlike a clean structural mirror, matching the two sides here needs explicit
`itable_rel`/`etable_rel` faithfulness facts (below), not just instance search.

**MIRROR (still mandatory where it applies):** fuel, the angelic exit/execute
choice, and the recursive step. **DON'T MIRROR (symbolic-only bookkeeping):**
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
proved by `iInduction` on fuel, GIVEN `itable_rel instrs tbl` and `etable_rel
exitCond exits` (table-faithfulness Pred-level premises: every key term
instantiates to a `SyncVal` address the gmap actually maps the same way). Its four
subgoals (`is_exit`/`lookup_instr`, hit/miss on each) are discharged sequentially
by hand rather than through `rsolve`/`refine_bind` pairing — see the divergence
note above.

In its lookup-hit branches, `destruct (lookup_instr ... )`/`instrs !! v`-shaped
matches can silently fail to reduce and stall `refine_bind` — that's a generic
stdpp-gmap pitfall; see the **gmap-pitfalls** skill for the mechanism and fix.
