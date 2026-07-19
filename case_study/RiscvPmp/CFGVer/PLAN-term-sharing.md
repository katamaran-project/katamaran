# PLAN-term-sharing — selective opaque naming at register writes

Status: PHASE 1 DONE — Plan A REFUTED, pivoting to Plan B (2026-07-19).
Root-cause context: memory note `project-key-schedule-loop-scaling`,
archive `.claude/archive/term-explosion-diagnosis-correction-2026-07-19.md`,
skills **cfgver-executor** ("Backward-branch loops") and
**core-executor-internals**.

> **Phase 1 outcome (throwaway branch `e2-term-naming-probe`, commit a81aab71):**
> - **E1 gate: PASSES by inspection.** No `combined_solver` stage re-substitutes
>   a `wco` equation into a later formula (RiscvPmp user solver = `tri_id`; the
>   generic solver never re-processes `wco`; `formula_simplifies` is syntactic-
>   eqb only). Write-time no-solver assume keeps `v=t` opaque *through the solver*.
> - **E2: Plan A INSUFFICIENT.** Prototyped `write_register` opaque naming;
>   naming provably fires, but `ValidCFGVerifierContract` stays at the baseline
>   exponential (~2.5×/trip, 17.6s @ N=4). Cause: `ValidCFGVerifierContract =
>   safeE (postprocess …)`, and `postprocess`'s `solve_uvars` eliminates the
>   named demonic vars **by substitution** (`uctx_subst`), re-inlining every
>   `v=t` inside the vm_compute (the E3 concern, biting early). The opaque name
>   must survive *every* elimination pass (`solve_uvars`/`solve_evars`/`solve_vc`),
>   not just the solver — pervasive.
> - **DECISION: go Plan B** (sharing-aware/memoized traversals) — attacks the
>   traversals directly, immune to re-inlining. Checkpoint with Dominique/Steven
>   before core implementation. Full detail in memory `project-key-schedule-loop-scaling`.

## Original Plan A draft (below) — kept for reference; superseded by the pivot above.

**Problem.** The symbolic executor's register store keeps raw unshared
`Term`s; an instruction sequence that rebuilds a register from k ≥ 2 copies
of its own previous value grows that term ~k^steps, and every traversal
(peval, Term_eqb, solver simplify, vm_compute) pays per SYNTACTIC OCCURRENCE
— Coq's physical value-sharing saves memory only, verified by probe (a
maximally-shared 3-copy mimic reproduced the exact ~3×/step blowup; an
opaque-marker contrast stayed flat at n=1000). Loops/trip counts are
orthogonal: straight-line code hits the same wall.

**Goal.** Symbolic-execution cost ~linear in executed instruction count,
independent of per-iteration register reuse, so `key_schedule_loop` (32-bit
analogue) verifies end-to-end at N=64 (2×32). Stretch: N=128.

**Out of scope.** The real 64-bit Botan `GHASH::key_schedule` ALSO needs the
separate relop-on-secret gap (`sltu` borrow chain — TODO.md "Botan CT::Mask /
64-bit-subtraction gap"). Orthogonal; not touched here.

**Core idea.** At each register-file write, if the written term is "large and
symbolic", store `term_var v` for a fresh logic variable `v` and record the
defining equation `v = t` in the path condition instead of the raw term.
Each instruction's terms are then size O(instruction body), not
O(accumulated history). Expressible with existing combinators (`demonic`
fresh var + assume), which shapes the soundness argument:
`∀v, v = t → P v ⊣⊢ P t`.

## Design constraints (the two known traps)

1. **Solver write-back.** `unify_pathcondition` eagerly turns `var = term`
   equations into triangular substitutions — inlining the definition right
   back. The naming path must bypass the solver
   (`assume_pathcondition_without_solver` plumbing exists), AND later solver
   calls must provably not pick the equation up out of `wco` and substitute
   anyway. Single biggest unknown → E1 gates everything.
2. **Dispatch-critical terms must stay transparent.** The pc is a register:
   naming `p+8` opaquely breaks `sexec_cfg_addr`'s syntactic `Term_eqb`
   table dispatch; naming a concrete loop counter breaks construction-time
   fork pruning (reintroducing a genuine 2^trips FORK blowup — the disproved
   original diagnosis would become true). Policy: name only when
   `term_get_val (peval t) = None` AND term size exceeds a threshold
   (pc arithmetic like `p+8` ≈ 3 nodes; one masking iteration ≈ 30+).
   Threshold preferred over a register allowlist — no ISA-specific knowledge
   in the core.

## Phase 1 — De-risk (experiments only, cheap)

- **E1 (solver behavior).** Scratch file against `SPureSpec` directly: add
  `v = t` to the path condition WITHOUT the solver, then run a later
  `assume_formula` on an unrelated constraint; inspect whether
  `combined_solver`/`unify_pathcondition` substitutes `v` from `wco`. If it
  does, find the smallest exemption (a marked formula kind vs. an
  unify-side skip predicate). **Decision gate: no clean exemption → Plan B.**
- **E2 (throwaway prototype).** Parallel `write_register`-with-naming
  definition (no soundness proofs, selected only in the CFGVer executor);
  re-run the scaling probe methodology (`Time vm_compute`/`Abort`, masking
  loop n=2..10). Expected ~linear. If not, the blowup has a second site
  (δ locals / mem-write results) — E2 locates it before any proofs are
  committed anywhere.

## Phase 2 — Real implementation (core, theories/)

- `name_term`-style combinator (`SHeapSpec`, delegating to `SPureSpec`):
  fresh var + no-solver defining equation + threshold/concreteness policy;
  integrate into `write_register` (and, if E2 implicates them,
  `assign`/mem-write results).
- Prove its `refine_*` lemma (compose `refine_demonic` + assume-formula
  reasoning; concrete counterpart is unchanged `write_register` — naming is
  concretely a no-op).
- Full-tree recompile (every case study, incl. MinimalCaps) is part of this
  phase, not an afterthought.
- **Checkpoint with Dominique/Steven before or during this phase** — their
  core combinator layer (TODO.md already flags telling them about the root
  cause); they may prefer to own the change or shape the formula-kind
  design. Load-bearing, not a courtesy: naming changes VC shape for every
  downstream consumer of the executor.

## Phase 3 — VC discharge adaptation (CFGVer)

- **E3 (discharge shape).** Check what `postprocess`/`safeE` do with a
  definition-chain VC — if postprocess substitutes definitions at the end,
  the blowup just moves to `solve_vc` time. The final goal must keep
  definitions as hypotheses (`intros v Heq` style), walked once.
- Extend `secLeak` residual handling: deriving `secLeak v` must go through
  `v = t` + the compositional `instprop_formula_secLeak_binop` on `t` —
  likely one new lemma + a `solve_vc` step.
- Update **cfgver-solve-vc**/**cfgver-executor** skills in the same commits
  as the behavior changes.

## Phase 4 — Regression + acceptance

- All existing examples stay green UNCHANGED (threshold policy should make
  naming a no-op for countdown/jumps/mvswap/cmovznz4/precompute — verify,
  don't assume).
- Parametric-base examples specifically (dispatch-transparency regression).
- **Acceptance:** `key_schedule_loop` (32-bit analogue) end-to-end
  noninterferent at N=64; record the new scaling curve. Stretch: N=128.

## Plan B — hash-consing / memoized traversals

If E1's gate fails, or Phase 2's refinement proofs turn out disproportionate:
make the PROCESSING side sharing-aware instead — memoize
`peval`/`Term_eqb`/simplifier over physically-shared nodes. More invasive
across theories/, but no solver-interaction problem. Decision point is the
end of Phase 1, not later.

## Risks

- E1 reveals the solver pervasively assumes substitutability of
  var-equations → Plan B early.
- vm_compute readback of the final VC can't exploit physical sharing if
  definitions leak into it → covered by E3.
- Threshold policy misjudged (something dispatch-critical exceeds it, or a
  duplicating term stays under it) → Phase 4 regression suite catches both
  directions; threshold is a tunable constant.
