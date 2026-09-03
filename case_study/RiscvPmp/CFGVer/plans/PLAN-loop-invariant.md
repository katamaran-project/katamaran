# PLAN-loop-invariant — per-iteration loop contracts for CFGVer

Status: **DESIGN, not started. Written 2026-08-10.** No code exists yet for
any phase below. This is a feasibility sketch turned into a trackable plan,
written at the request of the plan's owner after `PLAN-check-scalar-full.md`
§4's follow-up diagnosis pointed at a scaling mechanism neither of that
plan's two levers (`chunk_gc` widening, region chunks) cleanly fixes.

> **Evidence update (2026-08-14) — the premise is now measured on
> `key_schedule_loop2` too.** §0's `heap size × steps` mechanism was
> confirmed there, and separated from the "heap lookup is slow" reading it
> is easy to confuse with (`diagnostics/key-schedule-loop2-cost-drivers.md`,
> "Is the chunk cost SEARCHING or CARRYING?"). Varying data accesses per
> trip 0→1→2 at fixed heap size and fixed step count moves the
> declared-chunk excess by only 3.2%; moving the accessed cell to the
> opposite end of the heap changes nothing (1.002×); and the declared cells'
> predicate index (`ptstomem 4`) is matched by NO consume at all in the
> zero-access arm — never unified, never reaching the solver — yet they still
> carry 97% of the excess. The excess quadruples per doubling of N
> (3.81→4.08), i.e. exactly `H × S`. So the payoff claim below — asymptotic,
> `O(L·N²)` → `O(L·N)` — rests on measurement, and it comes specifically from
> **naming fewer resources**, not from touching them more efficiently.
>
> The carrier itself was already identified in `PLAN-byte-memory.md` §10
> (2026-08-05): `SHeap` is world-indexed with `Subst` via `subst_list`, so
> every world extension re-substitutes every chunk. Corollary for this plan:
> a map-backed `SHeap` or any indexing scheme cannot substitute for it —
> *not* because indexing was measured and found irrelevant to heap size, but
> because indexing addresses lookup, and lookup is not the cost. Commit
> `450d1118`'s ≤7% figure bounds LOOKUP only (it brackets the position of the
> matching chunk); do not cite it as a bound on the size cost.

Audience: a later session executing one phase at a time, same convention as
`PLAN-chunk-gc.md`. Each phase ends in an explicit GATE — reach it, report,
commit, stop. Do not run two phases in one sitting; this spans the soundness
chain and mistakes compound across phases.

---

## §0. What and why, in five lines

CFGVer's `gen_contract`/`sexec_cfg_addr` verifies a WHOLE program — loops
included — as ONE flat, fuel-unrolled VC, with every resource (e.g. all `N`
array cells) declared in ONE precondition up front. For `check_scalar`'s
loop 2 this makes cost scale like `L·N²` (heap size at each step × number of
steps), even though nothing leaks — see `PLAN-check-scalar-full.md` §4's
"Follow-up diagnosis." The fix: give the loop's **body** its own small
per-iteration contract (mentioning only the O(1) resources that ONE
iteration touches), and compose `N` copies of it via a hand-written Iris
induction — reusing CFGVer's OWN existing guarded-recursion machinery
(`myWP2_loop`) rather than inventing anything new. The composition SHAPE is
already proven and working elsewhere in this repo:
`MinimalCaps/LoopVerification.v`'s `valid_semContract_loop2`. Expected
payoff: turns `O(L·N²)` into `O(L·N)` — an asymptotic fix, not a
constant-factor one (contrast `chunk_gc` widening, which this repo's own
`Sig.v`/`GenContract.v` show is close to a no-op for these particular
non-duplicable chunks — see `PLAN-check-scalar-full.md`'s discussion — and
region chunks, whose payoff is real but whose implementation is a separate,
narrower, more invasive change; see that plan's §6).

---

## §1. Where the pieces come from — read before starting, in this order

1. **`Adequacy.v:106-153`** — `myWp2`, `myWP2_loop_fix`, `myWP2_loop`,
   `fixpoint_myWP2_loop_eq`, `exitCondImpliesMyWP2_loop`. This is the
   guarded-recursion object every per-iteration proof unfolds against:
   ```coq
   Definition myWP2_loop_fix (ExitCond : iProp Σ) (wp : myWp2) : myWp2 :=
     (ExitCond ∨
       ∃ v, pc ↦ᵣ SyncVal v ∗
       (pc ↦ᵣ SyncVal v -∗
        semWP2 [] [] (FunDef step) (FunDef step)
          (fun v1 _ v2 _ => match v1, v2 with
             | inr _, inr _ => True | inl v1, inl v2 => ▷ wp | _, _ => False end)))%I.
   ```
   Read this as "either exit, or take ONE machine step, then `▷`-recurse" —
   per-INSTRUCTION granularity, already built, already proved `Contractive`.
   Nothing here needs to change.
2. **`Adequacy.v:1248-1274`** — `sound_scfg_verification_condition_myWP2`.
   THE bridge lemma every CFGVer example's end theorem already goes through.
   Critically, it is **generic in `ExitCond`** — nothing about it assumes
   `ExitCond` is a program's REAL exit condition. This genericity is what
   lets Phase 2 below reuse it unchanged for a small, per-body VC instead of
   requiring a new soundness lemma.
3. **`MinimalCaps/LoopVerification.v:99-153,241-260`** —
   `Step_pre`/`Step_post`/`semTriple_step`/`valid_semContract_loop`/
   `valid_semContract_loop2`. The WORKING PRECEDENT for "verify one step,
   compose via induction into the whole loop." Note the difference from
   Phase 3 below: MinimalCaps uses `iLöb` (`:248`) because ITS loop
   (the interpreter's fetch-decode-execute loop) is genuinely unbounded.
   check_scalar's loop 2 has a known, fixed trip count (32), so Phase 3 uses
   **plain induction** on that bound instead — simpler, no coinduction
   argument needed at the TOP level (the ONE-iteration step itself still
   rides on `myWP2_loop`'s own `▷`, same as MinimalCaps' step does).

Context, not code, also worth having open: `PLAN-check-scalar-full.md` §4's
"Follow-up diagnosis" (the measurement motivating this) and §6 (region
chunks — the narrower, independent alternative this plan is not a
prerequisite for and does not block).

---

## §2. DECISION: which loop body, and Inv(u)'s exact shape

**Pick ONE instruction sequence and do not let later phases drift.**
`PLAN-check-scalar-full.md` §4 already flagged that loop 2 has TWO different
compiled forms: the standalone-compiled 13-instruction body
(`Example/ZZByteLoop2*.v`, `sltu`+`neg`/`or`) and the real
whole-function-compiled 16-instruction body (`check_scalar_instrs`,
XOR-based `GT`). **Phase 1 target: the standalone 13-instruction body.** It
is what the existing scaling measurement was taken against, it is already a
throwaway probe file (nothing to disturb), and it de-risks the technique
before spending it on the real body. Porting to the 16-instruction body is
a follow-up, not part of this plan's gates.

Per-iteration invariant, informally (concretely: an `Assertion` at the
per-iteration context, parametric in `u : nat`, `0 <= u < n`):

```
Inv(u) :=
    A0 ↦ᵣ (p + 52 + u) ∗ A1 ↦ᵣ (p + 52 + n + u) ∗ A2 ↦ᵣ (p + 52 + n + n) ∗
    A3 ↦ᵣ (accumulator value after u iterations, existential + secLeakvar) ∗
    ONE byte chunk for k[u] ∗ ONE byte chunk for n[u] ∗
    pc/nextpc ↦ᵣ (loop head address)
```

The load-bearing property, restated so it cannot be missed: **`Inv(u)` owns
exactly the CURRENT iteration's two byte chunks, not the whole array.** The
other `2(n-1)` byte chunks are NEVER mentioned by `Inv(u)` — they sit,
untouched, in whatever separately owns `gen_mem_pre_bytes`'s full assertion
at the OUTER (Phase 3) level, and get handed to the loop ONE cell at a time
as `u` advances. This is the entire mechanism that fixes the scaling: no
step of the per-iteration proof (Phase 2) ever carries more than O(1) chunks
through `sexec_cfg_addr`.

---

## §3. Model routing

| Phase | Model | Why |
|---|---|---|
| 1 — `Inv(u)` + the peel lemma | Sonnet | Separation-logic bookkeeping over `fold_right`/`big_sepL` — mechanical once the shape is fixed, but easy to get subtly wrong |
| 2 — the per-iteration WP fact | Sonnet | Configuring an existing call (`sound_scfg_verification_condition_myWP2` at small fuel, custom `ExitCond`), not inventing anything — but the fuel/exit-condition choice has a silent-completeness-loss failure mode (§7) |
| 3 — the outer composition | Sonnet, **high effort** | Hand-written Iris induction, modeled on `valid_semContract_loop2`. Where `▷`/framing mistakes are easiest and most expensive to find |
| 4 — wire into `EndToEnd.v` | Sonnet | Mechanical once Phase 3's output matches the `myWP2_loop ExitCond` shape every other example already produces and consumes |
| 5 — measurement | **Haiku runs, Sonnet/owner interprets** | Re-run the existing N=4/8/16/32 curve; same hard rule as `PLAN-chunk-gc.md` §3 — Haiku commits before measuring, quotes the commit hash, gates on `Finished transaction`, never reports from an uncommitted tree |
| 6 — gate + trusted-surface review | **Owner** | Axiom-clean allowlist unchanged; `Noninterference.v`/`Example/*Result.v` untouched unless this is deliberately meant to change the trusted statement (it should not be) |

---

## §4. The soundness argument — nothing new needed here, stated once

**Framing is sound by the ordinary separation-logic frame rule.** Splitting
`gen_mem_pre_bytes`'s `fold_right ∗`-built whole-array assertion into
"`Inv(u)`'s one cell, `∗`, the rest untouched" is not a new principle — it is
exactly what separating conjunction already licenses. No new axiom is
needed for it.

**`myWP2_loop`'s guardedness is not being modified.** Its `Contractive`
proof and `fixpoint` construction are existing, already-proved code
(`Adequacy.v`). Phase 3 only **invokes** this machinery at a smaller
granularity (once per loop iteration) than existing callers do (once for
an entire program run) — it is a new USE of an old proof, not a new proof
about the executor's semantics.

**Consequence:** no change is anticipated to `Noninterference.v`, `Sig.v`,
`Verifier.v`'s executor definitions, `myWP2_loop_fix`'s statement, or the
axiom allowlist. **If any phase below discovers it needs one of those
changed, STOP and report — that means this design sketch is wrong
somewhere, not that the fix needs a bigger hammer.** (Compare
`PLAN-chunk-gc.md` §2's "never reintroduce a flag" and the archived
world-GC's fate — a change to the trusted layer discovered mid-phase has
twice been the signal to stop and re-derive, not to push through.)

---

## §5. PHASE 1 — `Inv(u)` and the peel lemma

**Goal:** a standalone, provable statement that `gen_mem_pre_bytes`'s
existing whole-array assertion is equivalent to "the head cell, separately,
times the tail."

### What to build

1. Define `Inv_cell (addr_of : N -> Term Σ ty_xlenbits) (u : N)` — the
   `byte_chunks`-shaped assertion (`GenContract.v:203-208`) for exactly ONE
   word/4-byte entry at index `u`, matching `loop2_k_specs_rel`/
   `loop2_n_specs_rel`'s existing per-entry shape (`PLAN-check-scalar-full.md`
   §4's `ZZByteLoop2Common.v` — read it for the exact `addr_of` convention:
   a FUNCTION, not a base-plus-offset term, per that file's own comment on
   why nested `bvadd` breaks `peval` matching).
2. Prove, by induction on the `mem_spec_rel` list:
   ```coq
   Lemma gen_mem_pre_bytes_peel (specs : list mem_spec_rel) (s : mem_spec_rel) :
     gen_mem_pre_rel_bytes (s :: specs) ⊣⊢ gen_mem_asn_rel_bytes s ∗ gen_mem_pre_rel_bytes specs.
   ```
   This should already be true (or true after `cbn`) from `gen_mem_pre_rel_bytes`'s
   own `fold_right` definition (`GenContract.v:448`) — check whether it is
   already exactly this shape before writing a new proof; it may already
   BE `fold_right`'s unfold lemma for free (`fold_right_cons`-style).

### GATE 1

A throwaway probe (`Example/ZZLoopInvPeel.v`, not in `_CoqProject`, same
convention as every other `ZZ*` probe this project has produced) proving
`gen_mem_pre_bytes_peel` (or the `_rel_bytes` variant matching loop 2's
actual generator call) for a small concrete `n`. **Not yet wired into
anything downstream.** Commit and stop.

---

## §6. PHASE 2 — the per-iteration WP fact

**Goal:** `Inv(u) ⊢ (finitely many ▷) Inv(u+1)`, for `u+1 < n`, and a
separate closing fact for `u+1 = n` (exit).

### What to build

1. A **small VC**: call `gen_contract_rel_bytes` (or `scfg_verification_condition`
   directly, if the generator's assumptions about a full program don't fit)
   with:
   - `reg_specs`/`mem_specs` = `Inv(u)`'s shape (register offsets parametric
     in `u`; exactly `k[u]`, `n[u]` as the only memory).
   - `instrs` = the 13-instruction body ONLY (§2's decision).
   - `fuel` = 13 exactly — not 13+ǫ. This is the trap flagged in §7.
   - `exitCond`/`extra_exit_offs` = **"reached the loop head again"** (the
     BNE's target address), NOT the program's real exit. CFGVer's existing
     multi-exit machinery (`extra_exit_offs`, used by every example whose
     control flow leaves other than by falling off the end) is exactly the
     mechanism for this — nothing new to build here, just point it at a
     different address than usual.
2. Call **`sound_scfg_verification_condition_myWP2`** (`Adequacy.v:1248`)
   on this small VC's discharge, with a caller-chosen
   `ExitCondIprop := Inv(u+1)` (or, for the last iteration, the real
   program's exit-facing assertion). Its genericity in `ExitCond` (§1.2) is
   what makes this call legal without any new lemma.
3. The result is a WP fact of exactly the shape Phase 3 needs: `Inv(u)`
   (plus the small VC's own discharge) implies, after a FIXED, small number
   of `▷`s (matching the 13-instruction fuel), `myWP2_loop`'s continuation
   lands on `Inv(u+1)`.

### GATE 2

A lemma `loop2_body_step : forall u, u < n -> Inv(u) ⊢ ... Inv(u+1)` (exact
statement shape to be finalized once Phase 1's `Inv` is fixed), proved via
the route above, for a concrete small `n` first (e.g. `n = 4`) before
generalizing. Commit and stop.

---

## §7. PHASE 3 — the outer composition (the hard part)

**Goal:** `Inv(0) ⊢ myWP2_loop (RealExitCond)` for the WHOLE loop (all `n`
iterations), by plain induction on `u : 0..n`, chaining Phase 2's
per-iteration fact.

### What to build

Modeled directly on `MinimalCaps/LoopVerification.v:245-260`'s
`valid_semContract_loop2`, with the `iLöb` step replaced by plain `induction`
on the (known, fixed) remaining-iteration count:

```coq
Lemma loop2_composed (n : N) : Inv(0) ⊢ myWP2_loop RealExitCond.
Proof.
  (* induction on u = 0 .. n, NOT iLöb — n is a known bound, not unbounded *)
  induction u as [| u' IHu].
  - (* base case: u = 0, nothing to compose yet — or, reading it as
       induction on REMAINING iterations n - u, u = n is the base case
       (exit) — pick whichever direction makes the step case cleanest;
       MinimalCaps inducts "forward" via Löb precisely because it has no
       bound to count DOWN from, but n's fixedness here means either
       direction is legitimate; recommend counting u UP toward n so the
       final case reuses the SAME per-iteration lemma uniformly rather
       than needing a separate "last iteration" special case at u=0. *)
    ...
  - (* step case: use Phase 2's loop2_body_step to go from Inv(u') to
       Inv(S u'), then apply IHu (or the reverse, if inducting the other
       direction) — this is where the accumulated ▷'s from Phase 2's fact
       get discharged, exactly the iModIntro/wp_mono choreography
       MinimalCaps' valid_semContract_loop:133-151 already demonstrates. *)
    ...
Qed.
```

### GATE 3

`Inv(0) ⊢ myWP2_loop (RealExitCond)`, compiled and `Qed`-checked, for a
concrete small `n` (e.g. `n = 4`, matching Phase 2's gate). Commit and stop.
**Do not attempt the general `n` case in the same sitting as first getting
`n = 4` to compile** — get the shape right on the smallest instance first.

---

## §8. PHASE 4 — wire into `EndToEnd.v`

**Goal:** turn Phase 3's `myWP2_loop RealExitCond` fact into an axiom-clean
end theorem, in the same shape as every other CFGVer example.

### What to build

This should be close to mechanical: every existing example's end theorem
(`gen_contract_noninterferent`/`cfg_instrs_endToEnd`, `EndToEnd.v`) already
consumes a `myWP2_loop ExitCond` fact produced by
`sound_scfg_verification_condition_myWP2` applied to the WHOLE program's
flat VC. Phase 3 produces the SAME SHAPE of fact, just via composition
instead of one flat call. The wiring work is substituting Phase 3's proof
term where the existing machinery currently expects `sound_scfg_verification_condition_myWP2`'s
direct output.

### GATE 4

A new axiom-clean end theorem (e.g. `check_scalar_loop2_composed_noninterferent`,
in a new throwaway-then-promoted `Example/` file, same convention as
`PLAN-check-scalar-full.md` §3's Phase 2 outcome) for loop 2's 13-instruction
standalone body, at a concrete small `n`. Gate green, allowlist unchanged,
15th (or however many exist by then) end theorem.

---

## §9. PHASE 5 — measurement: does it actually fix the scaling

**This is the entire point of the plan — do not skip it, and do not trust a
prediction over a measurement (`PLAN-check-scalar-full.md` §8's own hygiene
rules apply here unchanged).**

Re-run the SAME N=4/8/16/32 curve `PLAN-check-scalar-full.md` §4 already
recorded for the flat-VC version, this time through Phase 4's composed
proof. **Expectation:** near-linear growth — the per-iteration VC's own cost
is now independent of `n` (Phase 1/2 fixed its footprint at O(1) cells), so
paying it `n` times should cost `O(n)` total, not `O(n²)`.

**If it is still superlinear:** STOP. Something in the framing broke and
`Inv(u)` is silently carrying more than the intended O(1) footprint — check
first whether Phase 1's peel lemma is actually being invoked at EVERY
induction step (Phase 3) or whether the composition accidentally
re-asserts the whole array at some point. This is exactly the kind of
mistake the "byte-identical census" discipline in `PLAN-chunk-gc.md` §12
was built to catch — consider borrowing that same census-equality technique
here (compare `vm_compute`/`Qed` cost curves is the primary signal, but a
census of the per-body VC's OWN size, independent of `n`, is a cheap
secondary check).

---

## §10. PHASE 6 — gate + trusted-surface review

- `scripts/gate.sh` (`GATE_JOBS=1`) green, axiom allowlist unchanged
  (`Machine.pure_decode`, `Base.mmioenv`).
- **No trusted statement changed.** Diff `Noninterference.v` and every
  `Example/*Result.v` — none should differ from before this plan started.
  This is an internal proof-STRUCTURE change (how the VC for one program is
  built), not a change to what is being proved.
- Update docs in the SAME commit: `PLAN-check-scalar-full.md` gets a
  pointer to this plan's outcome; this file gets a `LANDED` banner with the
  final measured curve; `cfgver-soundness`/`cfgver-executor` skills get a
  body update describing the new composed-proof option, gated through
  `skill-routing-maintenance` per this project's usual hygiene rule if any
  skill `description:` changes as a result.

---

## §11. Traps anticipated (design-time; update as phases land)

- **`▷` bookkeeping across `n` inductive steps.** An off-by-one in how many
  `▷`s Phase 2's lemma produces vs. how many Phase 3's induction step
  expects to strip shows up as a stuck `iModIntro`/unification failure at
  proof time, not a wrong theorem — Iris's own discipline catches this, but
  expect it to cost iteration time, same as MinimalCaps' own
  `do 2 iModIntro` (`LoopVerification.v:250`) needing to be exactly right.
- **Fuel mismatch** between the per-iteration VC's declared fuel and the
  ACTUAL body instruction count. Too tight: the small VC's own proof fails
  (a bare `False`, per `cfgver-solve-vc`'s "tight-fuel False" entry) —
  loud, not silent. Too loose (more fuel than the body has instructions):
  the executor may take an EXTRA angelic exit-vs-continue step past the
  intended loop-head landing point — check this explicitly at GATE 2, don't
  assume `fuel = instrs-length` is automatically exact.
- **Body-instruction-sequence drift** (§2): don't let Phase 4's real-body
  port silently mix the 13- and 16-instruction sequences.
- **`ExitCond`'s shape.** `myWP2_loop`'s `ExitCond` parameter is an
  `iProp Σ`, not a decidable Coq `Prop` — make sure Phase 2's "reached loop
  head" condition is phrased so the EXISTING `etable_rel`/`exitCond`
  table-of-exits machinery discharges it as-is, rather than inventing a new
  proof-obligation shape for "exited to address X" that duplicates what
  `extra_exit_offs` already does for every other example's non-fall-through
  exits.

---

## §12. Do NOT — scope boundaries

- **Do NOT attempt this for `key_schedule_loop` or any OTHER existing
  example as part of this plan.** check_scalar's loop 2 is the pilot.
  Generalizing into a reusable "loop contract" generator API (a sibling to
  `gen_contract`) is a natural follow-up but is explicitly out of scope
  here — land one concrete instance first.
- **Do NOT modify `myWP2_loop_fix`'s definition, its `Contractive` proof, or
  `sound_scfg_verification_condition_myWP2`'s statement.** Every phase here
  only INVOKES existing machinery. A phase that finds itself wanting to
  change one of these has drifted from the plan — stop and reconsider (§4).
- **Do NOT fold this into `PLAN-check-scalar-full.md`'s own phase numbering.**
  This is a separate, larger-scoped effort that plan's §5 whole-function
  decision does not need to wait on — cross-reference, don't merge.
- **Do NOT treat a successful Phase 6 as license to drop `chunk_gc`
  widening or region chunks from consideration for OTHER programs.** This
  plan fixes loop 2's specific scaling driver (heap-size × steps from an
  upfront-declared array); a program whose bottleneck is something else
  (e.g. genuine chunk leaks, as `encodes_instr` was) still needs the
  matching lever from `PLAN-chunk-gc.md`, not this one.

---

# UPDATE 2026-09-03 — the composition operator is PROVED, and §4/§6/§12 are wrong about scope

Written at the start of the loop-invariant session this plan was handed off to
(`diagnostics/base-k-hunt.md`'s "READ BEFORE THE LOOP-INVARIANT WORK" header is
the brief). Nothing in §5–§10's phase structure is retracted; what changes is
**what the phases have to touch**, and one premise of §0 needs restating under
the corrected cost model.

## U1. GOOD NEWS — `myWP2_loop` admits a bind rule, and it is 15 lines

The operator every flavour of contract composition needs — loop invariant,
straight-line segment cut, function contract — is monotonicity of `myWP2_loop`
in its `ExitCond`. It did not exist. It does now, **proved and compiled green**
(`Example/ZZLoopBind.v`, gitignored throwaway; ~7 min total including two
helper lemmas):

```coq
Lemma myWP2_loop_unfold (E : iProp Σ) :
  myWP2_loop E ⊢ myWP2_loop_fix E (myWP2_loop E).
Proof. rewrite {1}fixpoint_myWP2_loop_eq. done. Qed.

Lemma myWP2_loop_fold (E : iProp Σ) :
  myWP2_loop_fix E (myWP2_loop E) ⊢ myWP2_loop E.
Proof. rewrite {2}fixpoint_myWP2_loop_eq. done. Qed.

(* THE composition operator: if E1 (the first segment's exit assertion) itself
   implies "keep running until E2", then running until E1 and then continuing
   is running until E2. *)
Lemma myWP2_loop_bind (E1 E2 : iProp Σ) :
  ⊢ (E1 -∗ myWP2_loop E2) -∗ myWP2_loop E1 -∗ myWP2_loop E2.
Proof.
  iLöb as "IH". iIntros "HE H".
  iDestruct (myWP2_loop_unfold with "H") as "H".
  iEval (rewrite /myWP2_loop_fix) in "H".
  iDestruct "H" as "[HE1 | H]".
  - by iApply "HE".
  - iApply myWP2_loop_fold. iEval (rewrite /myWP2_loop_fix). iRight.
    iDestruct "H" as (v) "[Hpc Hcont]".
    iExists v. iFrame "Hpc". iIntros "Hpc".
    iDestruct ("Hcont" with "Hpc") as "Hwp".
    iApply (semWP2_mono with "Hwp").
    iIntros (v1 ? v2 ?) "Hm".
    destruct v1 as [v1|m1]; destruct v2 as [v2|m2]; try done.
    iNext. iApply ("IH" with "HE Hm").
Qed.
```

Notes for whoever lands this for real:

- It is **generic** — no CFGVer vocabulary, no table, no VC. It belongs next to
  `exitCondImpliesMyWP2_loop` in `Adequacy.v` (which is the `E ⊢ myWP2_loop E`
  unit of the same monad; `myWP2_loop_bind` is its bind).
- The `▷` bookkeeping §11 anticipated as the hard part **is one `iNext`**. The
  Löb IH lands exactly on the `▷ wp` in `myWP2_loop_fix`'s `inl/inl` branch.
- Two traps, both costing a compile. (1) A bare
  `rewrite fixpoint_myWP2_loop_eq` **also rewrites inside the Löb hypothesis**,
  because in IPM the hypotheses are part of the goal term — the IH then reads
  `(E1 ∨ …) -∗ (E2 ∨ …)` and `iApply "IH"` fails with
  `iSpecialize: cannot instantiate … with (myWP2_loop E1)`. Hence the directed
  fold/unfold pair plus `iEval (…) in "H"`. (2) `fixpoint_myWP2_loop_eq` has the
  fixpoint on BOTH sides, so the helper lemmas need occurrence selectors
  (`{1}` unfold, `{2}` fold) — same shape as `Adequacy.v:146`'s own proof.
- `rocq_start(theorem=myWP2_loop_bind)` reported the main lemma green while both
  helper lemmas were **broken** — `theorem=` replays the prefix vos-style and
  skips proof bodies. Exactly `rocq-implementation` §1's documented trap; the
  confirming `mode="full"` compile is what caught it.

## U2. BAD NEWS — §4 and §12 are wrong: the soundness bridge MUST change

§4 claims "nothing new needed here" and §12 says "Do NOT modify
`sound_scfg_verification_condition_myWP2`'s statement". §6 builds on that,
proposing to call it with `ExitCondIprop := Inv(u+1)`. **That call cannot be
made.** Read the bridge's actual conclusion (`Adequacy.v:1362-1374`):

```coq
⊢ ∀ a, asn.interpret pre … ∗ ⌜secLeak a⌝ ∗ pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs -∗
    (∀ an, ⌜exitCond an⌝ ∗ pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs -∗ ExitCond) -∗
    myWP2_loop ExitCond
```

`ExitCond` is indeed a genuine parameter, so §1.2's genericity claim is CORRECT.
But to *obtain* `myWP2_loop ExitCond` you must supply a continuation proving
`ExitCond` from **only** `pc`, `nextpc` and `ptsto_instrs`. Instantiating
`ExitCond := Inv(u+1)` therefore requires proving the loop-carried resources out
of nothing. The registers and memory cells `Inv(u+1)` names are gone: they were
handed to `produce req` at entry and never returned.

**Why they are gone is precise, and it is a wiring decision, not a limitation.**
The postcondition channel exists all the way down and is deliberately trivial:

| layer | what it does with the postcondition |
|---|---|
| `Verifier.v:1309` `sexec_triple_addr` | ends in `consume ens δ3.["an" ↦ na]` — the channel EXISTS |
| `Contracts.v:117` `CFG_VC_triple` | passes `asn.formula (formula_bool (term_val ty.bool true))` — i.e. `True` |
| `Contracts.v:132` `CFGVerifierContract` | has **no postcondition field** at all |
| `Adequacy.v:1288` | runs `cexec_triple_addr … (λ _ _, True) []` — final continuation discards the exit heap |

So CFGVer today proves "this program is safe and leaks nothing", never "and it
ends in state Q". Composition needs the latter, and only at the cut points.

**Revised scope, three changes, none touching the trusted statement surface:**

1. **`Adequacy.v` (heavy branch, the real work).** Strengthen
   `sound_cexec_triple_addr_myWP2` / `sound_scfg_verification_condition_myWP2`
   so the `ExitCond` continuation also receives
   `asn.interpret post ι.["a"↦a].["an"↦an]`, by threading a non-trivial shallow
   continuation instead of `(λ _ _, True)`.
2. **`myWP2_loop_bind`** — done, U1 above.
3. **Light chain**, mechanical: a postcondition field on `CFGVerifierContract`,
   passed by `CFG_VC_triple` instead of `True`. Default it to `True` so the nine
   live examples and `gen_contract` are unaffected.

`sexec_cfg_addr` itself, `myWP2_loop_fix`, `Noninterference.v` and every
`Example/*Result.v` stay untouched — §4's instinct was right about the
executor and the trusted surface, wrong only about the bridge. Keep §12's other
prohibitions.

## U3. §0's payoff argument needs restating — the mechanism it cites was retracted

§0 and the 2026-08-14 evidence update rest on cost `~ H·S` with a **superlinear
chunk exponent** (`H^(1+ε)·S`). That exponent is **RETRACTED**
(`check-scalar-combined-cost-drivers.md` §6.6, isolating grid): chunk count is
**exactly linear** — held-out linear fit 0.00% at 4× the heap size — and the
superlinear factor is `|Σ|`, which enters quadratically. So do not reuse "each
added chunk raises the cost of carrying every other one."

**The `O(L·N²) → O(L·N)` claim nevertheless survives, for a simpler reason.**
Cost is bilinear `H·S`, linear in each. A flat fuel-unrolled loop VC has
`H ≈ h₀ + cN` (all N cells declared up front) and `S ≈ sN` (N trips of the
body), so the product is quadratic on the diagonal. A per-iteration contract has
`H = O(1)` and `S = body`, both **independent of N**, and the executor runs it
ONCE — the N-fold repetition moves into a cheap Iris induction. The asymptotic
claim is if anything stronger than §0 states.

Two further reasons the case is now better than when this plan was written:

- **`drop_fuel=8` pins peak `|Σ|` at 33 regardless of program length**, and
  since the `var_dead` fix that is free (1.87× throughput, 2.66× footprint at
  K=206, both growing with K). That retires the `|Σ|` axis and leaves program
  length as the sole target. **Still ungated** — see the handoff TODO.
- **`Base(K)` — instructions plus the live `SymProp` tree — is 62% of peak
  footprint and rising**, `mlen=2` dies on memory, and *no* lever in the
  diagnostics catalogue touches it (`footprint-vs-throughput.md` §2.4).
  Composition attacks it directly: peak becomes the **max** over segments
  instead of the **sum**.

## U4. The pilot target should probably change

§2 fixes the pilot as check_scalar loop 2's 13-instruction body. Since then the
actual blocker moved: `PLAN-muladd-full.md` Phase 3 is BLOCKED, `mlen=2` dies on
memory, and the identified cost is `br_divrem`'s own loop (67.5 s for 2 trips in
isolation) called from a per-limb outer loop. That is a **doubly** favourable
shape — the inner loop wants an invariant, and `br_divrem` wants a *function*
contract applied at its call site. §12's "check_scalar loop 2 is the pilot, do
not generalize" still stands as scope discipline, but note the payoff now lands
on muladd, and pick the pilot with that in mind.

## U5. Before building anything — the ONE probe that bounds the payoff

The handoff's method lesson ("bound the candidate with a probe before building
the fix"; every candidate reasoned about from code alone was wrong or
negligible) applies here, and there is a specific cheap probe.

The K sweep at constant `|Σ|`=33 (`dropk-firing-payoff.md` ADDENDUM PART 2) has
alloc 452 → 1946 M words and peak RSS 0.30 → 1.08 GB for K 140 → 206 — 4.3× and
3.6× for a 1.47× rise in K, i.e. marginal cost per instruction (22.6 M) about
**7× the average at K=140** (3.2 M). That looks like strong superlinearity in
program length, which is what composition would remove. **But it is a PREFIX
sweep and the muladd prefix is structurally heterogeneous** (adjacent equal-width
windows swing 2.2×), so the later instructions may simply be intrinsically
costlier rather than made costlier by the ones before them. The two readings
predict different payoffs and the measurement cannot tell them apart.

**The probe that can:** take a FIXED instruction segment and measure its VC cost
standalone versus as the TAIL of a longer prefix, at constant `|Σ|`. Same design
as §6's `ZZSkipCommon` inventory swap (identical executed work, different
declared context), one axis moved.

- Fixed segment costs the SAME either way ⟹ cost is linear in K, and
  composition buys **footprint only** (peak vs sum) — which is still exactly the
  `mlen=2` wall, but it makes the cheaper unannotated alternative
  (`footprint-vs-throughput.md` §3: must the VC be built whole before `solve_vc`
  consumes it?) the better first move, since it buys the same thing with no
  annotation burden and no soundness work.
- Fixed segment costs MORE in context ⟹ composition buys throughput too, and
  the three-change programme in U2 is justified on its own.

Run this before Phase 1.
