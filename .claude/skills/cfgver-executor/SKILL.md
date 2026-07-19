---
name: cfgver-executor
description: >
  Katamaran CFGVer symbolic executor & verification condition — the decision layer.
  Use when reading or writing the symbolic side of the CFG verifier: sexec_cfg_addr
  (symbolic executor over a term-keyed instruction table), the angelic exit/execute
  choice at each step, why execution errors on a pc that matches no table key
  (lookup_instr/is_exit fail), ptsto_instrs / ptsto_instrs_lookup (instruction-memory
  ownership, still gmap-based on the concrete side), and scfg_verification_condition
  (how the VC is built and called). ALSO use when vm_compute on a backward-branch
  loop example genuinely never terminates (not just slow — no residual ever appears
  to even inspect) after its trip count was raised, especially if a SMALLER trip count
  on the same loop shape compiled fine — a known exponential (O(2^trip-count)) blowup
  from the core executor's demonic_finite/demonic_pattern_match unconditionally forking
  on every branch, not a fuel/timeout/spec-size problem to tune around. Contrast: a
  SINGLE vm_compute call that DOES finish and solve_vc then leaves a bare False (fuel
  merely too tight, not an exponential trip-count blowup) stays cfgver-solve-vc's
  territory, not this. NOT for the concrete mirror executor cexec_cfg_addr or
  rsolve/relational proofs (cfgver-refinement), and NOT for the VC-to-leakage chain
  (cfgver-soundness).
---

# CFGVer symbolic executor & VC

The decision layer of the verifier: what the symbolic executor computes and how the
VC is assembled from it. The concrete mirror (`cexec_cfg_addr`) and the proofs
relating the two live in **cfgver-refinement**.

## Instruction store

Two representations, one per side. The **concrete** executor (`cexec_cfg_addr`,
**cfgver-refinement**) still keys off a **`gmap (bv xlenbits) AST` by absolute pc**,
built by `instrs_of_list (bv.of_N init_addr) i` (`Tables.v`) from a plain `list AST` —
lookup is exact, `instrs !! v`. The **symbolic** executor (`sexec_cfg_addr`, below)
instead keys off a **term-indexed table** (`SInstrTable`/`SExitTable`, a `list (Term _
ty_xlenbits * AST)` resp. `list (Term _ ty_xlenbits)`) so that a symbolic pc like
`p + 8` can still be dispatched: matching is syntactic (`Term_eqb` modulo `peval`),
not a concrete lookup. `itable_faith`/`etable_faith` (`Verifier.v`) are the Prop-level
facts tying a given table to the gmap at a valuation; the refinement proof
(`rexec_cfg_addr`, **cfgver-refinement**) is what lets the two sides' VCs
correspond.

## `sexec_cfg_addr`

```coq
sexec_cfg_addr (fuel : nat)
  : ⊢ SInstrTable -> SExitTable -> STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits)
```

At each step it takes an `angelic_binary` (existential choice) between **exiting**
and **executing** the instruction at the current pc
(`angelic_binary m1 m2 Φ h = m1 Φ h \/ m2 Φ h`). Unlike a gmap lookup, `apc` never
needs to be concrete: `lookup_instr`/`is_exit` match it against the table's key terms
via `Term_eqb (peval apc) (peval key)`, so a literal base (`256+8` folds to `264`) and
a symbolic one (`p+8` matches the key term `p+8`) both work. `tbl`/`exits` are
threaded as recursion ARGUMENTS (not fixed `Fixpoint` params, since they're
world-dependent) and persisted across each step via `persist_itable`/`persist_etable`.

It stops with `error` when:
- `fuel = 0`
- `lookup_instr tbl apc = None` — the pc matches no table key (no instruction there)
- `is_exit exits apc = false` on the exit branch (chosen but no exit key matches)

## Backward-branch loops: exponential blowup, not a fuel/spec-tuning problem

A concrete-pinned-trip-count loop (`countdown`, `countdown_mem`,
`key_schedule_loop2`) does **not** scale past a small trip count by just raising
`fuel`/timeout — confirmed (2026-07-19) by trying to bump `key_schedule_loop2`
(N=2) to N=64: `vm_compute` alone (before `solve_vc` even runs) didn't finish in
590s. A finer timing probe (trip counts 1..8, `vm_compute` only, `Abort` before
`solve_vc`) showed a clean ~2–2.5× blowup per +1 trip (4→5→6→7 trips:
25.5s→52.2s→112.4s→285.5s — doubling, not polynomial), and a follow-up probe
ruled out `gen_mem_pre_rel`'s memory-precondition size as a factor (an 8-entry
table with a 2-trip loop was just as fast as the N=2 baseline; only the trip
count matters).

**Root cause is in Katamaran's CORE generic executor, not CFGVer.** A backward
branch like `BNE` has ordinary `if: taken then … else …` semantics
(`RiscvPmp/Machine.v`'s `fun_execute_BTYPE`), which desugars to
`stm_pattern_match` on a bool. The generic executor's handler for that
(`theories/MicroSail/SymbolicExecutor.v`'s `stm_pattern_match` case) calls
`demonic_pattern_match` (`theories/Symbolic/Monads.v`), whose fallback case
(`demonic_pattern_match'`) calls `demonic_finite (PatternCase pat)`, and
`demonic_finite F := demonic_list (finite.enum F)` — this **unconditionally
enumerates every pattern case** (both `true`/`false`), with no `peval`/
decidability check on the scrutinee first, even when it is already a concrete
`term_val`. The `assume_formula` that later constrains which fork is actually
consistent runs *after* the fork, so it prunes the resulting *proof
obligation*, not the *term being built*. Since `sexec_cfg_addr` continues the
full remaining fuel budget from **both** forks independently (its
`sexec_instruction i apc ;; sexec_cfg_addr n' ...` bind), every backward branch
the loop revisits doubles the term: O(2^(branch instructions within the fuel
budget)), i.e. O(2^trip-count) for a loop. For the underlying core-framework
mechanism itself (`demonic_finite`/`demonic_pattern_match`, their refinement
lemmas, why this affects any case study, not just CFGVer) see
**core-executor-internals**; for the general "my compile/proof is way slower
than expected" triage workflow that led here, see **rocq-timeout-triage**.

This is a property of the generic executor (any `if`/pattern-match on a
not-yet-reduced-but-decidable condition forks unconditionally) — `countdown`/
`countdown_mem` simply were never pushed past a tiny trip count before to
expose it. Two real (nontrivial) ways forward if a bigger concrete-trip-count
loop is ever needed: (a) teach `demonic_finite`/`demonic_pattern_match` (or a
specialized call site) to `peval` the scrutinee first and skip dead cases when
already concrete — a change to core `theories/Symbolic/Monads.v`, framework-
wide, needs real scrutiny before touching it; or (b) a genuinely different VC
shape for concrete-trip-count loops (induction/loop-invariant style, not
inline step-by-step unrolling) — the not-yet-designed *symbolic iteration
count* approach `TODO.md`'s `GHASH::key_schedule` entry already flags as open.
Session detail (the two isolating probes, exact timings): memory
`project-key-schedule-loop-scaling`.

## `ptsto_instrs`

```coq
Definition ptsto_instrs (instrs : gmap (bv xlenbits) AST) : iProp Σ :=
  ([∗ map] a ↦ i ∈ instrs, interp_ptsto_instr (SyncVal a) (SyncVal i))%I.
```

Access one instruction with `ptsto_instrs_lookup instrs v Hlk`
(`Hlk : instrs !! v = Some i`, via `big_sepM_lookup_acc`; `i` is implicit).

## `scfg_verification_condition`

```coq
scfg_verification_condition {Σ : LCtx}
  (req : Assertion (Σ ▻ "a"∷ty_xlenbits))
  (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits))
  (fuel : nat)
  (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
  (w : World) : 𝕊 w
```

Call pattern: `scfg_verification_condition (Σ := [ctx]) req tbl exits fuel ens wnil`.
`Σ := [ctx]` must be explicit — Coq cannot infer it. `tbl`/`exits` are given at the
CONTRACT context Σ (like `req`/`ens`) and substituted into the current world via
`subst_itable`/`subst_etable`. This is the VC every `CFGVerifierContract` actually
builds (`Contracts.v`'s `CFG_VC_triple`) — including fixed-address examples, whose
table entries are just literal-term keys.

**Postconditions are trivial by design**: `SHeapSpec` has no leakcheck — resources
left in the heap after consuming `ens` are silently dropped (affinely, in Iris).
`CFGVerifierContract` therefore exposes no postcondition field; `CFG_VC_triple` uses
the trivially-true assertion as `ens`, and the soundness lemmas discard the final heap.

For the parametric-base story specifically (why a *term*-keyed table rather than a
gmap in the first place), consult the "PARAMETRIC-BASE SUPPORT — READING GUIDE"
comment blocks in `CFGVer/Verifier.v` / `CFGVer/GenContract.v` and memory
`project-cfgver-symbolic-base-poc`.

**Next layer up:** the concrete mirror and the relational proofs are in
**cfgver-refinement**; the VC→`myWP2_loop`→leakage bridge is in **cfgver-soundness**.
