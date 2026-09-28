# PLAN — array invariants for loop blocks, 2026-09-28

Status: **DRAFT rev 2, awaiting Emiel's review.** Nothing built.
Rev 2 (same day): the ghost lemmas no longer live in `Machine.v` (trusted
statement) but in a CFGVer-local ghost annotation; the generic iterated chunk
was considered and rejected (see "Rejected alternatives").

## Goal (Emiel's words)

"We had the same problem when we were doing composition without annotations.
Adding support for this kind of invariant is the only future-proof approach."

The problem: an `ai_loop` block's invariant is its contract's precondition,
an `Assertion` over a FIXED logic context. A loop over an array with a
SYMBOLIC trip count owns a number of cells that depends on the count, and the
assertion language (`formula`/`chunk`/`chunk_angelic`/`pattern_match`/`sep`/
`or`/`exist`; `ptstomem`'s width is a Coq `nat`) cannot say "c cells". So
every sliding-footprint loop (muladd's D, I, K, M) is inexpressible as a loop
block today; only register-only loops (countdown, muladd's G) fit. This is the
same wall `loop_carry`/`loop_reservoir` hit at the Iris level (§R11 of
PLAN-muladd-composed.md, and "a CFGVerifierContract's post can never mention n
cells" in PLAN-segment-generators).

First target: loop D (memmove, muladd idx 84-89), the hardest of the four
because source and destination overlap.

## Decisions taken (2026-09-28)

- **A1. Ownership only.** Array chunks own cells with EXISTENTIAL values and a
  Coq-level public/private flag (public = every cell's value is `SyncVal`).
  No list-valued payload, hence no "the two runs have lists of different
  length" case in the binary model. Cannot state functional facts ("D shifted
  the array") -- not needed for noninterference.
- **A2. No `Machine.v` change.** `Machine.v` is imported by `Noninterference.v`,
  i.e. it is inside the trusted statement, and must not change for
  verification purposes (Emiel). So split/join are NOT Katamaran ghost lemmas
  (`𝑳 := Lem` is declared in Machine.v's program kit) but a CFGVer-local
  ghost annotation, see D2.
- **A3. `Sig.v` gets the predicates.** Sig.v is outside the trusted
  statement's imports (Noninterference.v requires only Notations, Bitvector,
  Semantics, RiscvPmp.Machine); its predicates enter only through the Iris
  interpretation, which is proved sound. Emiel: "not totally off-limits".
- **A4. Stride is a Coq-level parameter**: every predicate takes
  `(pub : bool) (s : N)`. Sig.v is the expensive rebuild, so generality is
  bought once.
- **A5. The pointer/count tie is a pure fact, closed as a RESIDUAL by `ring`.**
  `peval` has no linear normal form for `bvmul` (only the `bvmulx` mask
  patterns), so `e = dp - s*c` survives the solver; the back edge leaves a
  pure identity like `(dp-4) - 4(c-1) = dp - 4c`, closed by a new residual
  closer in `solve_param_vc` using `bv.ring_theory` (Bitvector.v:1603). Check
  the residual's actual shape (it may be over RelVal) in Phase 0. Upgrade
  path, if residuals multiply: a linear bv normal form in peval/Solver.v.
- **A6. BOTH indexings.**
  - count-indexed `arr_dn`/`arr_up` (addr, count) for COUNTER-driven loops
    (D): pop legality is `c ≠ 0`, free; the multiplication appears only in the
    post's ghost tie (A5).
  - endpoint-indexed `arr_rng lo hi` (cells lo, lo+s, ... below hi) for
    POINTER-bounded loops (K, M latch on `bne T5, S0`): pop legality is
    `lo ≠ hi`, exactly the latch; no count, no multiplication.
  Either indexing alone forces the multiplication into the other loop kind.

## Design

### D1. Three predicate families in Sig.v

    arr_dn  pub s  [p; n]    cells p, p-s, ..., p-s(n-1)   (top, walks down)
    arr_up  pub s  [b; n]    cells b, b+s, ..., b+s(n-1)   (base, walks up)
    arr_rng pub s  [lo; hi]  cells lo, lo+s, ... below hi

All args `ty_xlenbits`; precise on the first (address) argument, the second
as output, so an ordinary consume matches by address and the solver equates
the count/bound. Not duplicable. Every split/join moves an address by a
CONSTANT `±s`: no `s*c` with symbolic c ever reaches an address term.

### D2. The ghost annotation (CFGVer-local, replaces Katamaran ghost lemmas)

A new `Annot` kind in `Verifier.v`, next to `AnnotLemmaInvocation`:

    AnnotView {Δ} (pre post : Assertion Δ)

"consume `pre`, produce `post`", with `Δ` bound angelically by the consume --
`call_lemma`'s shape without an `LEnv` entry and without patterns. The
executor trusts it on the light side; its VALIDITY (`∀ ι, interpret pre ι ⊢
interpret post ι`) rides in `AnnotInstrV` and is discharged on the heavy side,
exactly as block validity does (PLAN-valid-blk-annot). The views used below
are instances of a handful of GENERIC entailments proved once per family.

Binding (why angelic is enough for split/join): `pre` consumes the ARRAY
chunk first, with `asn.chunk_angelic` -- only `consume_chunk_angelic`
(Monads.v:858) has the `heap_extractions` fallback. The array is the only
chunk of its predicate+flag+stride in the heap, so there is no real choice,
and it binds the address; the neighbouring cell is then consumed PRECISELY at
`a ± s`, a term after peval.

| view | statement |
|---|---|
| `dn_pop`    | `arr_dn p n ∗ n≠0 ⊢ (∃w, p ↦ₘ w) ∗ arr_dn (p-s) (n-1)` |
| `dn_push`   | `arr_dn a n ∗ (∃w, (a+s) ↦ₘ w) ⊢ arr_dn (a+s) (n+1)` |
| `up_cons`   | `arr_up a n ∗ (∃w, (a-s) ↦ₘ w) ⊢ arr_up (a-s) (n+1)` |
| `up_uncons` | `arr_up b n ∗ n≠0 ⊢ (∃w, b ↦ₘ w) ∗ arr_up (b+s) (n-1)` |
| `rng_pop_lo`/`_hi`, `rng_push_lo`/`_hi` | the same four over `[lo; hi)`, legality `lo ≠ hi` |

(pub variants add `secLeakvar w`.) No wrap side conditions: bv arithmetic is
modular, so the index shift is a ring identity, and a push/cons whose count
wraps to 0 has `emp` on the right, which holds by affinity.

### D3. ACCUMULATOR invariant, not a recursive post

A recursive post ("all c+1 cells") needs a FOLD after the back edge's block
returns -- a ghost with no instruction to hang it on (the block resumes at the
loop's exit, outside its code), i.e. a new "ghost after firing" hook in the
executor + refinement + soundness. Avoided by the tail-recursive shape: the
written cells accumulate IN the invariant, the post is a trip-invariant
function of ghost logic variables, and the back edge passes it through
unchanged.

Loop D (`lw S1,-4(S0); addi T6,T6,-1; addi S2,S0,-4; sw S1,0(S0); mv S0,S2;
bnez T6`), context `q` (code base), `dp`, `c`, `k`, ghost `e`, `N`:

    inv  := S0 ↦ᵣ dp ∗ T6 ↦ᵣ c ∗ c≠0 (public: dp, c)
          ∗ arr_dn priv 4 (dp-4) c        -- sources not yet moved
          ∗ (∃w, dp ↦ₘ w)                 -- the destination of this trip
          ∗ arr_up priv 4 (dp+4) k        -- already moved
          ∗ ⌜e = dp - 4c⌝ ∗ ⌜N = k + c⌝   -- tie the ghosts to the state
    post := S0 ↦ᵣ e ∗ T6 ↦ᵣ 0 ∗ (∃w, e ↦ₘ w) ∗ arr_up priv 4 (e+4) N

Views: `dn_pop` before the `lw`; `up_cons` after the `sw`. The ties are
written in SOLVED form (`e = …`, `N = …`) so the consume at the back edge can
instantiate the angelic ghosts; the leftover obligation is the ring identity
of A5. `arr_dn … 0` left at exit is dropped (affine).

### D4. Binary interpretation

`arr_dn pub s p n` := `[∗ list] i ∈ seq 0 (unsigned n), ∃ w, ptstomem (p - s·i) w`
(`w` SyncVal when `pub`), similarly for the others; `False` when the address
or count is a `NonSyncVal` -- the count must be public, which is exactly the
property that makes the loop cuttable at all (PLAN-muladd-composed §2).

## Relation to the previous machinery (Iris-level composition)

This is NOT a new decomposition. `GenCompose.v` already has it, at the Iris
level:

| GenCompose (LoopSpec route) | this plan (loop-block route) |
|---|---|
| `loop_reservoir A iota q n` (:1081), big-sep over `seq 0 n`: trips not reached | `arr_dn` |
| `loop_completed A iota q n N` (:1407), trips already run | `arr_up` |
| `Fr n := loop_reservoir … n ∗ loop_completed … n N` | D3's `inv` |
| `loop_reservoir_peel` / `loop_completed_push` | `dn_pop` / `up_cons` |
| the cell trade `Hc` (`loop_cells_trade`), a hand-written Iris proof per loop | done by the executor + solver |

**Why the old route needed no new predicates.** It took its trip count from
the META-logic (`myWP2_loop_induction` inducts on a `nat n`, trips indexed by
`iota : nat -> Valuation`), so each VC was one trip over a fixed window, and
the size-dependent part stayed an `iProp` frame (`Fr n`) outside the
executor, where Iris can say "n cells" natively. The price was the per-loop
Iris glue between trips. The loop-block route has no "between trips" in the
meta-logic: the back edge is inside one executor run, so everything the body
touches on any trip must be in the executor's heap, i.e. a CHUNK. The new
predicates are the price of moving the framing into the executor, which is
what PLAN-rec-loop-block asked for.

**What carries over.**
- **The soundness proofs.** D4 interprets the chunks as `big_sepL` over
  `seq`, exactly like `loop_reservoir`, so the generic view entailments are
  `loop_reservoir_peel` / `loop_completed_push` again (`seq_S`,
  `big_opL_app`, `big_sepL_cons`). Keep the interpretation in that shape ON
  PURPOSE.
- **§R11's vacuity lesson.** A reservoir whose cells overlap is `False`, so
  every lemma about it "proves" from an unsatisfiable premise. Same risk here:
  a count large enough to wrap the address space makes an array overlap
  itself. The entailments stay sound, but an invariant could become
  unsatisfiable without any test noticing. Hence the ENTRY CHECK in Phase 1.
- **Gone:** the per-loop trade (the executor does it), and the across-trip
  disjointness criterion of §R11 (the chunks of D3 are disjoint by
  construction, given no wrap).
- **Dissolved, not solved:** §R11's D blocker was a uniform width-2 window
  at every trip, whereas trip 0 touches one cell. With a count-indexed chunk,
  width is DATA, not shape, so the mismatch does not arise.

**What the old route had and this plan loses: generality.** `loop_reservoir`
takes ANY per-trip cell shape. `arr_*` are single-word cells at a Coq-level
stride (A4). That covers D/I/K/M (I and K's two arrays become two chunks).

## Rejected alternatives

- **Ghost lemmas in `Machine.v`** (rev 1). Katamaran declares `𝑳 := Lem` in
  Machine.v's program kit, so a `Lem` constructor would edit the trusted
  statement's text for a verification convenience. Replaced by D2.
- **A register parameter to locate the array** (`havoc_regs`-style).
  Rejected by Emiel: it "forces the machine state to be a certain way just
  for the proof technique to work".
- **A generic iterated chunk in `theories/`** (`loop_reservoir` as a `Chunk`
  constructor, with a body predicate). Would have avoided Sig.v and covered
  any per-element shape. Rejected as too complicated for what it is worth:
  ~64 `Chunk` matches across theories/ (Syntax/Chunks.v 35, Symbolic/Monads.v
  7, Refinement/Monads.v 7, UnifLogic.v 5, Shallow/Monads.v 5) plus ~15 in
  the case study, and a body with a bound element variable does not fit
  `GChunk V`'s uniform value parametrisation (`Term (Σ ▻ a)` symbolically vs
  a function concretely). A body-free version (`[∗ a ∈ lo..hi) ∃vs, p (a ::
  vs)`) fits, but still pays the full theories/ blast radius.
- **An integer-indexed body** (`cell (base + s·i)`): splitting would need
  linear bv normalisation of `s·(i+1)`. Address-indexed bounds avoid it.

## Open questions

- **Q1. INTRODUCING an array needs a term argument.** `⊢ arr p 0` (or
  `cell a ⊢ arr a 1`) has no array to match: its address is either an
  unconstrained angelic variable (which no later precise consume can equate
  with `dp`) or an angelic choice among ALL cells in the heap (ambiguous).
  Split/join never needs this, since each consumes an existing array; only
  the CALLER-side conversion from concrete cells does (Phase 3). So Emiel's
  "ghost variable" suggestion is needed there: `AnnotView` whose `pre`/`post`
  may mention the enclosing contract's logic variables. That makes the
  annotation context-indexed; decide in Phase 3 whether to index `Annot` by
  the contract's context or to name contract variables some other way.
- **Q2. Does `AnnotView`'s validity belong in `AnnotInstrV` alongside
  `blkValid`, or as a separate per-view side condition of
  `ValidCFGVerifierContract`?** The first reuses PLAN-valid-blk-annot's seal;
  check that `eraseV` and `annotsValid` extend without touching the trusted
  surface.

## Files touched

| file | change | side |
|---|---|---|
| `RiscvPmp/Sig.v` | three `Predicate` constructors, `𝑯_Ty`, precise, dup | forces the whole RiscvPmp rebuild |
| `RiscvPmp/IrisInstance.v`, `ModelBinary.v` | interpretation | heavy |
| `CFGVer/Verifier.v` | `AnnotView` + its `sexec_ghost` arm | light |
| `CFGVer/VerifierRel.v` | `cexec_ghost` arm + refinement (pet cannot open this file: probe-file workflow) | heavy |
| `CFGVer/Adequacy.v` / `Validity.v` | view validity in `AnnotInstrV`/`annotsValid`, soundness of the ghost step | heavy |
| `CFGVer/GenCompose.v` (or a new heavy file) | the generic view entailments | heavy |

No `theories/` change. No `Machine.v` change. No trusted-surface change
(Noninterference.v, `*Result.v` statements, `*_instrs`/`*_specs` untouched).

## Phases (each ends in a GATE: reach it, report, commit, stop)

- **0. Spike, light side only.** Sig.v predicates (all three families, ONE
  pass) + `AnnotView` in Verifier.v with its symbolic arm; Iris side stubbed
  only if the build forces it. Probe `Example/ZZArrD.v`: D standalone as an
  `ai_loop` block with D3's invariant, `solve_param_vc` (+ the ring residual
  closer). GATE: VC green AND two negative controls REJECTED (an invariant
  that drops `up_cons`'s cell; a wrong `N`). Settles D2's binding claim and
  A5's residual shape before any Iris work.
- **1. Interpretation, view entailments, ghost soundness.** D4; the generic
  entailments; `cexec`/`rexec` arms and the ghost step's soundness; view
  validity in the seal. GATE: `make Results.vo` green, axiom-clean; ENTRY
  CHECK: the interpretation of D's `inv` at a concrete count is inhabited.
- **2. D end-to-end standalone.** `ZZArrDResult.v` via `cfg_instrs_endToEnd`,
  like CountdownRecResult. GATE: axiom-clean end theorem.
- **3. D inside muladd.** The caller's side: converting muladd's concrete
  cells into `arr_*` chunks (Q1's context-indexed views). GATE:
  `bc_run_in_muladd`-style run of D at idx 84.
- **4. K, then I, M** on `arr_rng`. Two arrays per loop, one private (x[])
  and one public (m[]): different flags, so each view still has one
  candidate. GATE per loop as Phase 0.

## Risks

- **Angelic ambiguity** (D2): two arrays with the same predicate, flag and
  stride give the consume an `angelic_list` choice per view. Wrong choices
  should fail at the next precise consume, but cost is unmeasured. Measure in
  Phase 0/4.
- **Ring residuals** (A5): the residual may be stated over RelVal, where
  `ring` does not apply directly; restating the ties over `unsigned` in
  `ty.int` is the fallback.
- **peval on `(dp + -4) + 4`**: invariant re-establishment needs the cons'd
  address to fold back to `dp`; `try_bvadd_cancel_*` should do it -- check in
  Phase 0 before relying on it.
- **Rebuild cost**: Sig.v sits under everything RiscvPmp. Batch every Sig.v
  edit into one pass (GATE_JOBS=1 on this box).
- **VerifierRel.v cannot be opened by pet**; the refinement arm for
  `AnnotView` needs the probe-file workflow the ghost-refinement work used.
