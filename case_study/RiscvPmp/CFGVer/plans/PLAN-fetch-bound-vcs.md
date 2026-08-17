# PLAN-fetch-bound-vcs — stop emitting the per-address access-bound VCs

Status: **DONE 2026-08-17. Phases 1–3 complete; GATE 1, GATE 2 and GATE 3 all
reached.** Landed in commit `aa4ccdf4`. Written 2026-08-17. Successor to the
`formula_propeq` cancellation that landed 2026-08-16
(`diagnostics/check-scalar-combined-cost-drivers.md` §5.5) — same shape of fix,
next target down the ranking.

**Outcome in one line:** the per-address bound VCs are gone (residuals 29 → 0
at m4n4, 37 → 0 at m4n8), the fix reaches **99.5% of Phase 1's measured
ceiling** — 4.32× / 3.34× / 2.73× at diagonal N=4/8/16 — and `./scripts/gate.sh`
passes with the 14 end theorems still axiom-clean. Full record:
`diagnostics/check-scalar-combined-cost-drivers.md` §5.8 (the ceiling) and
**§5.9** (the landed fix). Post-fix the symbolic-base penalty is 1.55–1.73×,
down from 4.0–6.7×, so the base is no longer a major multiplier and
**`chunks × steps` is now the sole driver** — which is `PLAN-loop-invariant.md`.

**Read §0.1 before quoting any speedup**: the headline is a CONSTANT factor
that shrinks with N (2.34× at the real `klen = 32`, ~0.64 of a doubling in
reachable N), not an exponent change. The wall is moved, not removed.

Audience: a later session doing ONE phase at a time. Each phase ends at an
explicit GATE — reach it, report, commit, stop.

**Read first:** `diagnostics/check-scalar-combined-cost-drivers.md` §5.5
(the residual dump and what the goals actually are), §6.5 (the cost law and
where this sits in the ranking), and the `cfgver-solve-vc` skill (the
`relval_fetch_*` lemma family — the mathematics this plan RELOCATES rather
than invents).

---

## §0. Before anything: what this is worth, honestly

The `cfgver-scaling-diagnostics` skill requires three statements before a fix
gets funded. Here they are, and the third is the one to keep in view.

1. **Predicted end-to-end win.** ~~Up to **~4×** at N=32 on the parametric base
   if the per-address obligations are eliminated entirely. Derived, not
   guessed: at m=n=32 parametric costs 116.21 G and the same program at a
   concrete base — which emits none of these obligations — costs 28.82 G. The
   whole gap is 4.0×, and these VCs are the bulk of what differs. At smaller N
   the gap is larger (6.7× at N=4), so the win shrinks as N grows.~~

   **RETRACTED 2026-08-17 by Phase 1's own measurement — never requote the 4×.**
   The reasoning above assumed the base's ENTIRE cost is these VCs, which §2
   was written to test and which is false: at N=32 only **76%** of the
   parametric penalty is the obligations, the other 24% being symbolic address
   terms that no VC work touches. Measured ceiling, by deleting the obligations
   at source (`diagnostics/…` §5.8): **2.34× at m=n=32**, 2.74× at N=16, 3.36×
   at N=8, 4.33× at N=4. The share itself decays ≈4.8 points per doubling,
   because the obligations are per-ADDRESS (linear in N) while cost is
   `H^(1+ε)·S` (superlinear) — so this mechanism is a shrinking fraction of the
   whole *by construction*, and any figure for it must name its N. In headroom
   terms: at 3.76× cost per doubling, 2.34× buys **0.64 of a doubling** in
   reachable N. A real solver rule lands strictly below that ceiling, since it
   still builds `unsigned (off ⊕ p)` before simplifying it away and pays a
   recognizer on every formula.

   **CORRECTED 2026-08-17 after Phase 2 landed.** The last sentence was wrong
   in practice: the real rule lands at **99.5–99.6% of the ceiling** at every
   size measured, i.e. the recognizer plus the discarded term-building cost
   together are ~0.4%, not a meaningful shortfall. The reason is the outermost
   `int_bound_shape` guard — only an already bound-shaped `≤` pays for the
   `wco` scan, so the rule costs nothing on the formulas it cannot serve
   (measured: a concrete-base program is unchanged to four significant
   figures). The ceiling figures themselves stand.
2. **Constant factor or exponent change?** A **CONSTANT FACTOR.** It does not
   touch `H^(1+ε)·S`. After this lands, chunks × steps is 100% of the growth
   and the curve's shape is unchanged. Anyone hoping this makes the wall go
   away should read §6.5 first.
3. **Is the mechanism still dominant afterwards?** No — and that is the point.
   Post-fix the base is the LARGEST remaining multiplier but not a scaling
   term; removing it promotes chunks × steps to sole driver, which is what
   `PLAN-loop-invariant.md` addresses. These two plans compose: this one buys
   a constant, that one buys the exponent. **Do this one first only because it
   is far smaller** — see §2's estimate — not because it matters more.

A fourth statement, specific to this repo's history: the owner has chosen to
keep the parametric base (`PLAN-check-scalar-full.md` §5). This plan is how
you make the parametric base cheap **without** trading it away, so it is
aligned with that decision rather than a workaround for it.

---

## §1. What exists today (VERIFIED 2026-08-17)

### The obligations

After `vm_compute; solve_vc`, **every** residual on a parametric-base VC has
one shape — an access upper bound:

```
0 ≤ lenAddr − (K + unsigned (offset ⊕ p))
```

with `K = 4` for a 4-byte instruction fetch and `K = 1` for an `LBU` byte
access, `p` the symbolic base, `offset` a literal. Nothing else survives.
Measured on the two-loop rig at m=n=4: **29 residuals = 17 instruction
addresses + 12 byte addresses**, i.e. exactly one per distinct address the
program touches. A concrete base emits **none** (the `unsigned` of a literal
computes), which is why `solve_vc` there is 0.21 s against 9.32 s parametric.

### They are all implied by ONE hypothesis already in the precondition

`gen_contract_rel(_bytes)` (`GenContract.v:469-472`) puts a base bound in the
precondition:

```coq
asn.formula (formula_relop bop.le
  (term_binop bop.plus (term_unop uop.unsigned (term_var "p"))
                       (term_val ty.int (Z.of_N bound)))
  (term_val ty.int (Z.of_N lenAddr)))
```

For any address the program touches, `offset + K ≤ bound` holds by
construction of the contract. So every residual follows from that single
hypothesis by linear arithmetic **plus a no-wrap step**: `bvadd` wraps, so
`unsigned (offset ⊕ p) = offset + unsigned p` needs `unsigned p + offset <
2^32`, which the base bound gives (`lenAddr ≤ 2^32`).

### The mathematics is ALREADY PROVED — this plan relocates it

`Contracts.v`'s `relval_fetch_upper_bare` / `relval_fetch_upper_add` /
`relval_fetch_lower` do exactly this reasoning, including the no-wrap step,
and `solve_symbase_fetch` applies them one goal at a time. **So no new
mathematics is expected.** If a phase turns up some, that is a
STOP-and-report event, not something to improvise (this repo has a recorded
incident of axiomatising a goal to get a green build — see
`PLAN-check-scalar-full.md` §0.5).

The cost is that they are applied *per goal, after the fact*: the executor
builds `#addresses` obligations, `vm_compute` normalises them, `solve_vc`
splits them, and only then are they discharged. The parametric/concrete
`vm_compute` gap (9.32 s vs 3.71 s at m4n4) says roughly half the waste is
incurred before `solve_vc` even starts, so a faster *tactic* cannot recover
it — the goals must not be emitted.

---

## §2. Phase 1 — measure the ceiling before building anything

**GATE 1 REACHED 2026-08-17. Numbers and method:
`diagnostics/check-scalar-combined-cost-drivers.md` §5.8. Do not re-run this
phase; read that section instead.** Summary of what it settled:

- §2.1 **residual law confirmed on a third shape.** `residuals = 17 + m + 2n`
  predicted 37 at m4n8, measured 37. Both earlier points held n=4, so this is
  the first test of the `2n` coefficient. Still zero fitted parameters.
- §2.2/§2.3 **the `vm_compute` half is NOT mostly symbolic-term cost**, which
  was this phase's stop condition. It is **76%** obligation cost (±0.4 pts over
  three shapes), and `solve_vc` collapses to the concrete arm's value. Across
  both stages the obligations are 76–90% of the whole parametric penalty. So
  the plan is not re-scoped or dropped on those grounds.
- **The probe was NOT the `PVConst` pinning sketched below** — that doesn't
  isolate anything, since a `PVConst` base *is* a concrete base and moves both
  axes at once. What worked: delete the three upper-bound conjuncts from
  `Spec.v` (`sep_contract_fetch_instr`, `sep_contract_mem_read`,
  `sep_contract_checked_mem_read`), leaving every address term symbolic and
  identical. Control: residuals go 29 → 0 at m4n4 and 37 → 0 at m4n8, so the
  ablation hits exactly the intended goals. That tree state is unsound (it also
  forces `valid_checked_mem_read` to `Admitted`) and was reverted and rebuilt.
- **What changed the decision:** not the share, but its N-dependence. §0.1's
  ~4× is retracted; the measured ceiling at the real `klen = 32` is 2.34×.

Original text of the phase follows, for the record.

**GATE 1: a number for "what fraction of the parametric penalty is these
obligations", and a decision to proceed or stop.**

§0's 4× is an upper bound that assumes the base's ENTIRE cost is these VCs.
That is not established. The base could also cost through bigger terms
everywhere (`p + off` vs a literal), which no amount of VC elimination fixes.

Cheapest discriminator, no new machinery: take a parametric contract and give
the base bound a form that makes the obligations trivially closable, or
compare against a concrete-base run instrumented to count. Concretely:

1. Count residuals as a function of program shape — already have m4n4 = 29,
   m8n4 = 33; confirm the law is `#distinct addresses` on a third shape.
2. Split the parametric/concrete gap into its `vm_compute` and `solve_vc`
   halves at two sizes (have m4n4: 9.32/9.32 vs 3.71/0.21). The `solve_vc`
   half is unambiguously the obligations. The `vm_compute` half needs one
   more probe to attribute — a parametric run whose addresses are all
   *literal* (base pinned by `PVConst` rather than symbolic) isolates
   "symbolic address terms" from "bound obligations".
3. State the split. **If the `vm_compute` half is mostly symbolic-term cost
   rather than obligation cost, the ceiling is well under 4× and this plan
   should be re-scoped or dropped.**

Model: **Haiku** — mechanical probe replication plus `/usr/bin/time`, per
`PLAN-check-scalar-full.md` §0.5's routing. Paste raw output; never type a
number from memory (that plan records a fabricated-measurement incident).

---

## §3. Phase 2 — discharge the bound in the SOLVER, not in a tactic

**GATE 2 REACHED 2026-08-17 — residuals 29 → 0 (m4n4) and 37 → 0 (m4n8), no
new axioms, `Solver.v` fully proved. Landed as written below, with two
corrections worth knowing before touching this code again:**

- **The recognizer must NOT compare two `unsigned` operands across widths.**
  `Equations` refuses ("the pattern n2 should be equal to n1, it is forced by
  typing"), both for two pattern-bound widths and for a parameter/pattern pair.
  Land the data in NON-dependent form instead — `unsigned_bvadd_split` returns a
  `Z`, a `Term Σ ty.int` and a plain `nat`, rebuilding `unsigned s` so the
  caller compares at `Term Σ ty.int` where `Term_eqb` is homogeneous. Two
  ~6-minute builds were spent learning this; definitions inside
  `GenericSolverOn` cannot be reached interactively.
- **§3.3's soundness obligation needed no `secLeakT` guard at all.**
  `instprop_formula` sends a NonSyncVal operand to False on the HYPOTHESIS too,
  so over a secret base the base bound in `wco` is itself False and the
  entailment is vacuous. Stronger than the `formula_propeq` rule's argument.

**Original text of the phase follows.**

**GATE 2: m4n4's residual count drops from 29 to ~0, with the same VC
otherwise, and no new axioms.**

Mirror `try_bvadd_cancel_propeq`, which is the closest working precedent:

1. A recognizer for the bound shape — `formula_relop bop.le (term_val 0) …`
   over `lenAddr − (K + unsigned (bvadd (val off) s))`, handing back
   `(K, off, s)`. Keep the guard cheap and syntactic; this runs on every
   formula the solver sees.
2. A path-condition lookup for the base bound on the same `s`, in the style
   of `secLeakT`'s `pathconditions_contains_secLeakT` (`Solver.v:224`) —
   i.e. "does `wco w` contain `unsigned s + B ≤ lenAddr`", returning `B`.
3. Discharge to `empty` when `off + K ≤ B`; **fall through untouched
   otherwise.** Never `error` here: failing to find the bound means "cannot
   decide", not "false". Getting this backwards would make the solver refute
   satisfiable paths, which is unsoundness in the dangerous direction.
4. Wire into `simplify_formula`'s `formula_relop` arm alongside the existing
   `try_bvadd_cancel` dispatch.

**Do the work interactively.** `rocq-implementation` §1's rule is now
hook-enforced: check each change with `rocq_start(preamble=…)` + `rocq_check`
before compiling `Solver.v`. Six full rebuilds were burned on 2026-08-16
ignoring exactly this, on the sibling lemma.

Soundness obligation, mirroring `try_bvadd_cancel_propeq_spec`: `instpred d
⊣⊢ instpred (formula_relop …)` for the `empty` case, which reduces to the
no-wrap argument `relval_fetch_upper_add` already carries. Expect to reuse
that lemma rather than reprove it.

---

## §4. Phase 3 — end-to-end and gate

**GATE 3 REACHED 2026-08-17.** `./scripts/gate.sh` passes — build clean, no
holes, 14 end theorems axiom-clean (only the whitelisted `Machine.pure_decode`
/ `Base.mmioenv`). Diagonal re-measured at N=4/8/16 (**4.32× / 3.34× / 2.73×**,
99.5–99.6% of the ceiling); **N=32 post-fix was NOT measured** — that point
costs ~400 s at ~9 GB and the machine was RAM-constrained, so §5.9's N=32 row
is inferred from the thrice-confirmed ratio and marked as such. All 12
`Example/*.v` compile with real `Qed`s. `solve_symbase_fetch` is now a no-op on
these examples and was LEFT IN PLACE per §4.2. Run the gate at `GATE_JOBS=1` on
a 14 GB box: the default `-j3` puts three ~3 GB `coqc` processes up at once and
makes the machine unusable.

**Original text of the phase follows.**

**GATE 3: `./scripts/gate.sh` green, and the cost numbers.**

1. Re-measure the diagonal N=4..32 on the parametric base and compare against
   §6.5's table. Report the achieved factor against §0's predicted ~4× — and
   if it is much less, say so plainly and record why, since §0's ceiling is an
   upper bound.
2. Confirm `solve_symbase_fetch` is now a no-op on these examples. If it is,
   **leave it in place** — it is the fallback for shapes the solver rule does
   not match, and removing it would turn a missed match into a hard failure.
3. `./scripts/gate.sh`. Note it now excludes `ZZ*` from the hole scan, so
   probes may stay in the tree.
4. Update `diagnostics/check-scalar-combined-cost-drivers.md` §6.5's ranking
   and this file's status in the same commit ("docs travel with code").

---

## §5. Risks, and one alternative that is probably worse

- **Solver-rule cost.** A recognizer that runs on every formula can cost more
  than it saves. Mitigate with a cheap outermost syntactic guard, and measure
  a program with NO such obligations (a concrete-base example) to confirm no
  regression there.
- **The `vm_compute` half may not be recoverable.** See §2.3. This is the
  main reason Phase 1 exists and must not be skipped.
- **Alternative considered and not recommended:** assert all per-address
  bounds in the precondition up front. It removes the obligations by making
  them hypotheses — but it lengthens the path condition by `#addresses`, and
  path-condition length is scanned by every solver call, so it trades a
  bounded one-off for a per-step cost. Given §6.5 shows per-step costs are
  what dominate, this looks like a net loss. Measure before believing it if
  anyone wants to try.
- **Do not weaken the statement to get a green build.** If the discharge
  cannot be proved, report why. `PLAN-check-scalar-full.md` §0.5 records the
  two incidents that make this worth restating.

---

## §6. What this plan explicitly does NOT do

- It does not touch `H^(1+ε)·S`. Growth shape is unchanged (§0.2).
- It does not remove `solve_symbase_fetch` (§4.2).
- It does not help a concrete-base contract, which has no such obligations.
- It does nothing for term growth, which is closed by `peval` recognizers and
  is fragile to new idioms in a way this is not (§6.5's ranking note).
