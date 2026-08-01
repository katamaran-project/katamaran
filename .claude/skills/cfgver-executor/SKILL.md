---
name: cfgver-executor
description: >
  Katamaran CFGVer symbolic executor & verification condition — the decision layer.
  Use when reading or writing the symbolic side of the CFG verifier: sexec_cfg_addr
  (symbolic executor over a term-keyed instruction table), the angelic exit/execute
  choice at each step, why execution errors on a pc that matches no table key
  (lookup_instr/is_exit fail), ptsto_instrs / ptsto_instrs_lookup (instruction-memory
  ownership, still gmap-based on the concrete side), and scfg_verification_condition
  (how the VC is built and called). ALSO use when a backward-branch loop example's
  vm_compute cost scales badly as its trip count is raised — it never terminates, or
  a SMALLER trip count on the same loop shape compiled fine. Two mechanisms, and the
  skill covers both: symbolic TERM DUPLICATION (the loop body rebuilding a register
  from k ≥ 2 copies of its own previous value; no term sharing in the executor's
  register store) is real but was measured NOT to be dominant at practical trip
  counts; the measured-dominant driver is the LIVE LOGIC-VARIABLE CONTEXT — two
  demonic variables per instruction step that are never unified away, so a loop whose
  every symbolic term is held O(1) by construction scales just as badly. Either way
  this is a structural scaling property of the executor, NOT branch forking and not a
  fuel/timeout/spec-size problem to tune around. Contrast: a
  SINGLE vm_compute call that DOES finish and solve_vc then leaves a bare False (fuel
  merely too tight, not a trip-count scaling blowup) stays cfgver-solve-vc's
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
instead keys off a **term-indexed table** so that a symbolic pc like `p + 8` can
still be dispatched: matching is syntactic (`Term_eqb` modulo `peval`), not a
concrete lookup.

**Two table types, and the distinction matters** (2026-08-01):

| type | shape | who sees it |
|---|---|---|
| `SInstrTable` | `list (Term _ ty_xlenbits * AST)` | CONTRACT level — what `table_of_list` builds, what `itable_rel` relates to the gmap, what `TablesRel.v`'s faith lemmas discharge |
| `SInstrTableW` | `list (Term _ ty_xlenbits * Term _ ty_word * AST)` | EXECUTOR only — `sexec_cfg_addr` runs on this |

The extra column is the raw instruction WORD. It exists because
`sep_contract_fetch_instr` used to hide the word behind an `∃`, minting a fresh
demonic variable on EVERY step; the word cannot be derived (`pure_decode` is an
uninterpreted `Axiom` with no injectivity), so it must be supplied per address.
`sexec_triple_addr` introduces the words ONCE by extending the context it already
hands to `demonic_ctx`, from `Σ` to `Σ ▻▻ words_ctx (length tbl)`, then
`zip_words` attaches them. Because the column lives on `SInstrTableW` and not on
the Σ-level `SInstrTable`, **`itable_rel`, the faith lemmas, `Contracts.v`,
`GenContract.v` and every example were untouched by the change.**

`itable_rel`/`etable_rel` (`VerifierRel.v`) are the guards tying a Σ-level table
to the gmap at a valuation; `itable_relW` is the fused, loop-carried relation the
executor's induction uses, DERIVED from them at the entry point (see
**cfgver-refinement**). The refinement proof (`rexec_cfg_addr`) is what lets the
two sides' VCs correspond.

## `sexec_cfg_addr`

```coq
sexec_cfg_addr (fuel : nat)
  : ⊢ SInstrTableW -> SExitTable -> STerm ty_xlenbits ->
      STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits)
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
- `lookup_instr tbl apc = None` — the pc matches no table key (no instruction there).
  Note `lookup_instr` returns `option (Term _ ty_word * AST)`: the raw instruction
  WORD and the instruction come from ONE lookup, so they cannot disagree.
- `is_exit exits apc = false` on the exit branch (chosen but no exit key matches)

## Backward-branch loops: exponential blowup = term duplication, not forking

> **`|wctx|` IS FIXED 2026-08-01, BUT IT WAS NOT THE SCALING DRIVER; read this
> first.** Both per-step demonic variables are gone and execution-driven
> `|wctx|` growth is now ZERO. `an` became a threaded contract parameter
> (`exec_instruction_prologue`); `encoded_instr` became a per-ADDRESS word
> supplied once via `SInstrTableW` (see the table-types section above).
> Measured on the flat `zzn` reproducer: survivors per trip **+15 → +1**, and
> that +1 is the reproducer's own `mv`. So do NOT re-diagnose `|wctx|` growth on
> a loop example — those per-step survivors no longer exist.
>
> **What this did NOT buy is a slope change.** An earlier version of this banner
> claimed "exponent 1.44 → 1.05, the curve bends". **Retracted:** that figure is
> `zzn_raw_nc`, i.e. VC construction plus a node census, excluding `solve_vc`,
> `solve_symbase_fetch` and `Qed`. Measured end to end with a real `Qed` on the
> same reproducer, the exponent at N=8→16 is **1.48 and rising**.
>
> Where the time actually goes (N=1/8/16, parametric base): `vm_compute`
> 1.01/14.28/39.77 (exp 1.48); **`solve_vc` 7.90/6.42/10.50 — FLAT, a fixed toll,
> never a scaling term**; `solve_symbase_fetch` over all goals <1 s; **`Qed`
> —/~10.4/35.12 (exp 1.76, 41% of the N=16 run)**. The driver is proof-term size
> — `vm_compute` plus KERNEL RE-CHECKING at `Qed`, which no probe in this whole
> investigation had measured.
>
> A **concrete** base (`gen_contract`) makes `solve_vc` 0.00 s with 0 goals left
> and is ~1.8× faster at N=16, but its exponent is **1.63, steeper**. So the
> symbolic base is a shrinking constant-factor penalty, not the driver — don't
> chase it expecting a slope change. `solve_vc`'s residuals under a symbolic base
> are all `0 ≤ 1024 - (4 + unsigned (p ⊕ off))`, one per instruction address plus
> the exit (15/22/30 at N=1/8/16, +1/trip for each iteration's store address);
> the `SyncVal p => p | NonSyncVal _ _ => False` wrapper is just how
> `formula_relop` prints and is NOT a secret-data wall.
>
> Ceiling on the dev box: N=16 completes, N=32 is earlyoom-SIGTERMed at 5.80 GB.
> Full record: `CFGVer/PLAN-encoded-instr.md` **§8-FOLLOWUP** (which supersedes
> §7-RESULTS' timing table) and `PLAN-nextpc-param.md`.
>
> The term-duplication mechanism below also remains unfixed, and was measured NOT
> to dominate at practical trip counts.
>
> **ROOT-CAUSED 2026-07-29 — historical, kept for the methodology.**
> The k^trip-count term-duplication mechanism described here is real and
> correctly diagnosed, but it is **not the dominant cost at practical trip
> counts**, so do not reach for term sharing / hash-consing / SSA naming on the
> strength of it. A/B with the program shape held identical to
> `key_schedule_loop2` and only the 10-instruction ALU chain swapped: a loop in
> which NO register's symbolic term ever grows (`addi a0,a1,1` ×10, A0 never
> written) costs the SAME as the real masking chain.
>
> **The measured driver is the live logic-variable context `|wctx|`.** Exactly
> two demonic variables per instruction step are introduced and never unified
> away, so `|wctx|` grows linearly in steps and per-emission cost grows with it:
>
> - `an` — `Verifier.v`'s own `exec_instruction_prologue`,
>   `asn.exist "an" ty_xlenbits (nextpc ↦ term_var "an")`.
>   *Measured:* introduced once per step, eliminated zero times.
>   *Inferred, NOT verified — check before building a fix on it:* the epilogue
>   consumes `pc ↦ an ∗ nextpc ↦ an`, which does relate `an` to the real pc, but
>   consumption yields an **angelic** equation (`assert_vareq`) while `an` is
>   **demonic**, and a demonic variable cannot be eliminated by an angelic
>   equation. The counts are consistent with that story (`angelicv` 169 ==
>   `assert_vareq` 169 per trip, i.e. angelic variables *are* all eliminated),
>   but the asymmetry itself was never directly confirmed.
> - `encoded_instr` — `Spec.v`'s `sep_contract_fetch_instr` postcondition.
>   Unification of `result_fetch = term_union … (term_var "encoded_instr")`
>   eliminates `result_fetch` *in favour of* `encoded_instr`, leaving it live.
>
> Every other variable the executor introduces IS eliminated cleanly
> (`result_decode`, `imm`, `rs`, `rd`, `op`, `result_rX`/`wX`/`tick_pc`, `a`,
> `w`: introduced == eliminated). Contract-entry existentials (`p`, `v*`, `mv*`)
> add a constant, not a per-step, amount.
>
> Evidence (single-variable interventions on the fetch postcondition, each
> controlled by a 12-counter node census; flat reproducer, N=4): `|wco|` ÷15 →
> **0.82×**; `|wctx|` ×1.97 → **2.19×**. Measured NOT to be the cause: node
> count (raw grows exactly +1389/trip while time grows superlinearly),
> `postprocess`/`erase_symprop`/`safeE` (free — the whole pipeline costs the same
> as raw construction alone), heap size (0.95× at N=4), `SymProp.debug` payloads
> (there are none — count is 0), and path-condition length (above).
>
> Also note: ~96.5% of built nodes are discarded (2801 raw → 99 final at N=2),
> and every `block` node is a solver-killed fork under a binary node (~410/trip).
> Discarding is free, so that waste is not worth optimising — but it does mean
> any ablation that weakens the solver causes path explosion; see
> **rocq-timeout-triage** Step 3b for how to control an ablation, and Steps
> 1c/1d for the measurement rules (one heavy `Eval` per process; force a stage
> with a cheap consumer rather than printing it). The earlier
> "N^2.6 with rising exponent" figure did NOT survive clean re-measurement and
> should not be quoted. Full record: the `project-key-schedule-loop-scaling`
> memory note.

A loop example does **not** scale past a small trip count by raising
`fuel`/timeout when its BODY rebuilds a (secret) register from k ≥ 2 copies of
that register's own previous value — cost grows ~k^trip-count. First hit on
`key_schedule_loop2` bumped to N=64 (2026-07-19: `vm_compute` alone >590s,
~2-2.5× per +1 trip); re-diagnosed by a probe chain the same day (scratch
methodology: `Lemma _ : ValidCFGVerifierContract (...). Proof. Time
vm_compute. Abort.` at trip counts 2..10 — an earlier fork-blowup diagnosis
was disproved and is archived in
`.claude/archive/term-explosion-diagnosis-correction-2026-07-19.md`):

- countdown (`X1 := X1 - 1`, ONE copy per iteration, backward BNE): flat to
  quadratic up to 10 trips in ALL generators — concrete, `_param`, `_rel`.
  Backward branches per se are fine; so is a store at an advancing pointer
  with private data (~linear).
- the full key_schedule masking body at CONCRETE base: ~2.5×/trip
  (2.4s→44s over n=2..5) — no rel/param machinery needed to reproduce.
- minimal pair: `A0 := A0>>1` flat at n=10; `A0 := (A0>>1) ^ (A0&1)` (TWO
  copies of A0) ~1.7×/trip at n=6..9. The real masking chain makes THREE
  copies of A0 per iteration.

**Mechanism (core framework, not CFGVer):** the generic executor's register
store holds raw `Term`s; each write stores the full expression, so a body
that references a register k times per iteration multiplies its term size by
k — no sharing/let-binding/hash-consing — and every later peval/solver pass
plus the final vm_compute pays linearly in that size. Path forking is NOT
involved: `demonic_pattern_match` does enumerate both BNE cases, but each
fork's `assume_formula` runs `combined_solver` at construction time, and a
refuted fork collapses to `SymProp.block` before its continuation is built
(details: **core-executor-internals**). Unrolling the loop does NOT dodge the
wall — term growth is a property of the instruction sequence, not the loop
encoding (3^128 for the real GHASH::key_schedule either way).

Diagnosis checklist: exponential-looking vm_compute scaling with trip count ⇒
count how many times the loop body reads registers holding growing symbolic
terms (secret/existential values; pinned public values fold to literals and
stay size-1). Fix directions (all nontrivial, tracked in TODO.md's
GHASH::key_schedule section): value naming/sharing at register writes (beware
`unify_pathcondition` substituting definitions back in), a loop-invariant /
symbolic-iteration-count contract shape (fresh symbolic register value per
iteration — also the only route to symbolic trip counts), or a sharing-aware
term representation. Probe data: memory `project-key-schedule-loop-scaling`;
general triage entry point: **rocq-timeout-triage**.

## `ptsto_instrs`

```coq
(* ptsto_instrs_w names the word at each address; ptsto_instrs keeps the old
   MEANING by existentially quantifying it, which is why ImplPre and the end
   theorems did not change when the word was threaded (2026-08-01). *)
Definition ptsto_instrs_w (words : bv xlenbits -> bv word)
    (instrs : gmap (bv xlenbits) AST) : iProp Σ :=
  ([∗ map] a ↦ i ∈ instrs,
     interp_ptsto_instr (SyncVal a) (SyncVal (words a)) (SyncVal i))%I.

Definition ptsto_instrs (instrs : gmap (bv xlenbits) AST) : iProp Σ :=
  ([∗ map] a ↦ i ∈ instrs, interp_ptsto_instr (SyncVal a) (SyncVal i))%I.
```

The soundness chain threads `ptsto_instrs_w words instrs` for a FIXED `words`
and re-packs to `ptsto_instrs` only at the outer boundary.
Access one instruction with `ptsto_instrs_lookup words instrs v Hlk`
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
