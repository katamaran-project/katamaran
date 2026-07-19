# PLAN-havoc-secrets — forget secret register values at writes

Status: DRAFT (2026-07-19). Successor to PLAN-term-sharing.md after its
Phase 1 refuted Plan A (opaque naming) — see that file's status header and
memory note `project-key-schedule-loop-scaling` for the full root-cause and
refutation record.

**Problem (recap).** The symbolic register store holds raw `Term`s; a loop
body rebuilding a secret register from k ≥ 2 copies of itself grows the term
~k^steps, and every traversal pays per syntactic occurrence. Plan A (store
`term_var v` + path-condition equation `v = t`) failed because
`postprocess`'s `solve_uvars` eliminates demonic vars **by substitution**,
re-inlining every definition inside the `ValidCFGVerifierContract`
vm_compute.

**Core idea.** At a register write of a *secret* value, store a fresh
demonic variable and record **no defining equation at all** — genuinely
forget the value ("havoc"). This is Plan A minus the `assume`:

- **Immune to re-inlining by construction.** `solve_uvars` substitutes
  definitions; a havoc var has none. Nothing any elimination pass does can
  resurrect the forgotten term. This kills the exact failure mode that
  refuted Plan A.
- **Sound by over-approximation.** Demonic = ∀: the VC proves the
  continuation for *every* value of the fresh var, in particular the real
  one. (Same argument as `refine_demonic` + instantiation.)
- **Complete for constant-time code.** `secLeak rv` holds iff the value is
  `SyncVal` (Formulas.v:117); a genuinely secret (`NonSyncVal`) value can
  NEVER satisfy it. So the precise term of a secret is unusable at every
  `assertSecLeak` site (Monads.v:436/452/577) anyway — forgetting it costs
  nothing, *provided the program never declassifies* (never turns secret
  intermediates back into provably-public values, e.g. by cancellation
  `k ⊕ (k ⊕ m) = m`). GHASH key-schedule qualifies: all secret flows end in
  private memory.
- **The framework already does this at entry.** `gen_reg_asn`
  (GenContract.v:92): a private register's precondition is
  `r ↦ᵣ term_var "v"` with *no* constraint — an entry-time havoc. The
  proposal only re-applies the same abstraction at writes, restoring the
  "secret = unconstrained fresh var" invariant every step instead of only
  at step 0. Per iteration the secret then costs O(body) (fresh var in,
  ~30-node term out, havoc'd again at the write) → total work linear in
  instruction count. Full flattening, not a smaller exponential base.

**Goal / out of scope.** Same as PLAN-term-sharing.md: `key_schedule_loop`
(32-bit analogue) end-to-end noninterferent at N=64, stretch N=128;
symbolic-execution cost ~linear in executed instructions. The 64-bit
`sltu` borrow-chain gap stays out of scope.

## The one hard design question: the havoc guard

Havoc must hit secrets and ONLY secrets:

- Havoc a **public** value → it loses its `secLeak`-provability → spurious
  failure at the next assert (branch on it, address from it, store of it to
  public memory). E.g. havoc'ing the pc breaks `Term_eqb` dispatch
  (observed in Plan A's unconditional-naming probe: instant `lookup_instr`
  failure); havoc'ing counter A4 would make the loop exit genuinely
  demonic → real fork blowup.
- Miss a **secret** → that register keeps accumulating and the exponential
  survives (E2 detects this: curve doesn't flatten).

Guard candidates, cheapest first:

1. **Concreteness + size threshold** (Plan A's guard, reusable as-is):
   havoc iff `term_get_val (peval t) = None` AND size > threshold. Keeps
   pc/counters transparent (concrete after peval). Risk: a *symbolic
   public* value above threshold gets wrongly havoc'd — none of today's
   examples obviously has one, but the parametric-base examples carry
   symbolic `p`-relative public terms (small, ~3 nodes — under any sane
   threshold). E2 sweeps the suite to find out if this is already enough.
2. **Syntactic taint**: havoc iff the term mentions ≥1 "secret-origin"
   variable. Seedable from the contract (vars introduced WITHOUT
   `secLeakvar`), propagated for free by occurrence. Precise but needs a
   taint set threaded through the executor (or recomputed from the
   pathcondition's `formula_secLeak` formulas at each write — slower but
   stateless). Only build this if E2 shows guard 1 misfires.
3. **Entailment query** (ask the solver "is secLeak t implied?") — most
   precise, most expensive, almost certainly overkill. Not planned;
   recorded for completeness.

## Phase 0 — Experiments (throwaway branch, no proofs)

All on a new throwaway branch off `e2-term-naming-probe` (commit a81aab71),
which already contains the patched `write_register` AND the probe harness
(`Example/ProbeE2Baseline.v`, sweep via `ks_regs`/`ks_mem_words`/fuel,
`Time vm_compute` + `Abort`). Budget note: each `theories/Symbolic/Monads.v`
edit costs a ~8-min vos rebuild — E1 is ONE edit; batch any further guard
tweaks.

- **E1 (does havoc flatten the curve?).** One-line delta: delete the
  `assume_formula_no_solver` line from the patched `write_register` (keep
  `demonic` + store `term_var v`; guard 1 with the existing
  `term_get_val (peval t) = None` check, threshold initially none — every
  symbolic write havocs). Re-run the scaling probe on the masking loop,
  N = 2..10, timing `ValidCFGVerifierContract` (the metric that refuted
  Plan A). Check BOTH:
  - (a) timing ~flat/linear in N, and
  - (b) the VC is still TRUE — `vm_compute; solve_vc` still discharges
    (prediction: yes — the loop's asserts touch only A4/A3/pc, all
    concrete, hence transparent; stored A0 goes to private memory, no
    `secLeak` asserted).
  **This gates everything.** ~1 rebuild + probe runs; the cheapest
  experiment in this whole saga.

- **E2 (is guard 1 enough for the suite?).** Same branch: `vos`-compile
  every existing example (countdown, jumps, mvswap, cmovznz4, precompute,
  parametric-base variants, countdown_mem) and re-run their
  `ValidCFGVerifierContract` lemmas. Classify each failure: (i) a public
  symbolic value got havoc'd (guard too coarse → need threshold tuning or
  guard 2), vs (ii) unrelated breakage (probe patch bug). Prediction:
  concrete-base examples all pass untouched (their public values are
  concrete); parametric-base examples are where a symbolic-public havoc
  could first appear.

- **E3 (acceptance preview).** With the guard settled by E2, sweep
  `key_schedule_loop2` to N=16/32/64 (contract fuel and table
  words scaled accordingly). Record the curve; N=64 discharging in
  seconds-to-minutes is the success signal.

### Decision tree

| Outcome | Meaning | Action |
|---|---|---|
| E1(a) fails: still exponential | Second duplication site (δ locals / mem-write results / pathcondition), same as old plan's E2 concern | Bisect with the minimal-pair probes (1-copy vs 3-copy bodies) to locate it; havoc the same way at that site; only if the site is un-havocable (e.g. inside the pathcondition itself) reconsider Plan B |
| E1(b) fails: VC now false | Something in THIS loop needs the precise secret value — would falsify the core completeness claim | Inspect the residual (`DebugCFGVerifierContract`); if it's a `secLeak` on a havoc'd var, the guard misfired (fix guard); if it's a genuine value-dependence, havoc is the wrong tool → stop and report findings, Plan B back on the table |
| E1 passes, E2 clean | Guard 1 (concreteness+threshold) suffices | Proceed to E3 then Phase 1 with guard 1 — smallest possible core change |
| E1 passes, E2 has class-(i) failures | Need secrecy info, not just size | Design guard 2 (taint set) in Phase 1; scope grows by the taint plumbing but the approach stands |
| E3 stalls before N=64 despite flat E1 | Linear-but-large constant (VC has ~14·N demonic binders + N stores) | Profile: if it's `solve_vc`/`postprocess` walking binders, that's Phase 3 work (discharge shape), not a refutation |

## Phase 1 — Design checkpoint (BEFORE any proofs)

Review the E1–E3 numbers and settle the design decisions before committing
to proofs:

- **Hook placement**: (a) core `SPureSpec.write_register` guarded havoc
  (smallest diff, but core-owned and affects every case study), vs (b) a
  CFGVer-local post-instruction pass in `sexec_instruction` (Verifier.v:164)
  that rewrites large/tainted `chunk_ptsreg` chunks in the heap
  (contained to the case study; core stays untouched; needs a small
  heap-rewrite combinator). (b) is the better story for upstreaming later;
  (a) is what the probe already validates.
- **Guard mechanism** (1 vs 2, per E2), and who owns the threshold
  constant.
- **Refinement direction sanity-check**: the claim that the concrete
  mirror can stay UNCHANGED — symbolic havoc-write refines concrete
  precise-write because the symbolic VC (∀v. post v) implies the concrete
  WP (post at the actual value) by instantiation. Verify this matches the
  `RefineCompat` direction before writing any proof; if refinement is
  stated in a shape that forces the concrete side to mirror the demonic,
  `CPureSpec.demonic` is ∀ over values and the end-to-end argument still
  instantiates at the real register value — either way sound, but the
  proof plumbing differs.
- Completeness restriction to document: **no declassification** — a
  program that legitimately turns secret intermediates into public outputs
  will spuriously fail under havoc. Fine for the GHASH family; must be
  written down as a CFGVer verifier restriction, not discovered later.

## Phase 2 — Real implementation

- The havoc combinator + guard at the chosen hook (per Phase 1). If core:
  `write_register` gains the guarded `demonic` branch (the probe code minus
  the assume, plus threshold/taint guard). If CFGVer-local: heap-rewrite
  pass after each instruction step.
- `refine_write_register` (Refinement/Monads.v:1498) variant: compose
  `refine_demonic` with instantiation; NO assume-formula reasoning needed
  (simpler than Plan A's obligation would have been).
- Thread through the relational soundness chain (VC → myWP2_loop →
  leakage): standard over-approximation step, but budget real time — the
  foundational proofs are always the long pole.
- Full-tree recompile (all case studies incl. MinimalCaps) if the core
  hook is chosen; CFGVer-only rebuild if local.

## Phase 3 — VC discharge adaptation (CFGVer)

- Havoc vars reach the final VC as plain demonic binders with no defining
  equation: `solve_uvars` has nothing to substitute (they survive as ∀),
  `solve_vc` must simply `intro` them. Verify no pass chokes on many
  binders (~14·N for the masking loop) — expected linear.
- A `secLeak` residual mentioning a havoc var can no longer be discharged
  compositionally (the `instprop_formula_secLeak_binop` route died with the
  term) — by design it should never APPEAR (guard prevents havoc of
  public values); if one shows up it signals a guard misfire or a real
  leak. Add a `solve_vc` failure message making that diagnosis obvious.
- Update **cfgver-solve-vc** / **cfgver-executor** /
  **core-executor-internals** skills in the same commits.

## Phase 4 — Regression + acceptance

- All existing examples green UNCHANGED (guard should make havoc a no-op
  for countdown/jumps/mvswap/cmovznz4/precompute — E2 already previewed
  this, re-verify with the final guard).
- Parametric-base examples specifically (symbolic-public transparency).
- **Acceptance:** `key_schedule_loop` end-to-end noninterferent at N=64;
  record the new scaling curve. Stretch: N=128.
- Negative test: a deliberately-leaky variant (store A0 to PUBLIC memory)
  must still FAIL — havoc must not have weakened the property. Add it as a
  `False`-VC regression alongside the tight-fuel ones.

## Risks

- **Declassification incompleteness** is inherent, not a bug — document
  it. If a future target needs declassification, that's a per-site
  "unhavoc/reveal" annotation design, out of scope here.
- Guard misjudged in either direction → E2 + Phase 4 regression catch
  both; threshold/taint-seed are tunable without touching proofs.
- Refinement direction surprise (Phase 1 sanity-check fails) → the
  concrete mirror gains a matching demonic; more proof plumbing but no
  soundness obstacle.
- Linear-but-large constants at N=64 (binder count) → Phase 3 discharge
  shaping; profile before optimizing.
