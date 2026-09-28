# PLAN — array invariants for loop blocks, 2026-09-28

Status: **DRAFT, awaiting Emiel's review.** Nothing built.

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
- **A2. Ghost lemmas find their array by ANGELIC heap matching**, not through a
  register (Emiel: a register parameter "forces the machine state to be a
  certain way just for the proof technique to work"). Lemma arguments must be
  constants anyway (`AnnotLemmaInvocation`'s `es` lives at the empty program
  context), so the lemma takes only Coq-level parameters (the pub flag) and
  its precondition's address/count are angelic logic variables resolved by
  `consume_chunk`'s `heap_extractions` fallback (Monads.v:831-884).
  FALLBACK if angelic choice proves ambiguous or costly: a new annotation kind
  whose arguments are terms over the contract's logic variables (a "ghost
  variable" argument). Heavier: Annot becomes world-indexed, touches executor,
  concrete mirror, refinement and soundness.

- **A3. Stride is a Coq-level parameter** (Q1, decided): every predicate and
  lemma takes `(pub : bool) (s : N)`. Sig.v is the expensive rebuild, so
  generality is bought now.
- **A4. The pointer/count tie is a pure fact, closed as a RESIDUAL by `ring`**
  (decided). `peval` has no linear normal form for `bvmul` (only the
  `bvmulx` mask patterns), so `e = dp - s*c` survives the solver; the back
  edge leaves a pure identity like `(dp-4) - 4(c-1) = dp - 4c`, closed by a
  new residual closer in `solve_param_vc` using `bv.ring_theory`
  (Bitvector.v:1603). Check the residual's actual shape (it may be over
  RelVal) in Phase 0. Upgrade path, if residuals multiply: a linear bv
  normal form in peval/Solver.v (theories/ change).
- **A5. BOTH indexings** (decided):
  - count-indexed `arr_dn`/`arr_up` (addr, count) for COUNTER-driven loops
    (D): pop legality is `c ≠ 0`, free; the multiplication appears only in the
    post's ghost tie (A4).
  - endpoint-indexed `arr_rng lo hi` (cells lo, lo+s, ... below hi) for
    POINTER-bounded loops (K, M latch on `bne T5, S0`): pop legality is
    `lo ≠ hi`, exactly the latch; no count, no multiplication.
  Either indexing alone forces the multiplication into the other loop kind.

## Design

### D1. Two DIRECTED predicates, count-indexed

    arr_dn pub p n   cells p, p-4, ..., p-4(n-1)     (top address, walks down)
    arr_up pub b n   cells b, b+4, ..., b+4(n-1)     (base address, walks up)

args `[ty_xlenbits; ty_xlenbits]`, precise on the address (input) with the
count as output, so an ordinary consume matches by address and the solver
equates counts. Direction is chosen so that every lemma moves by a CONSTANT
offset (+-4): no `4*c` with symbolic c ever reaches an address term, where
peval/the solver would have to normalise a symbolic multiplication.

### D2. Lemmas (ghost; `Lem` constructors carry only `pub : bool`)

| lemma | statement |
|---|---|
| `arr_dn_pop`   | `arr_dn p n ∗ n≠0 ⊢ (∃w, p ↦ₘ w) ∗ arr_dn (p-4) (n-1)` |
| `arr_dn_push`  | `(∃w, p ↦ₘ w) ∗ arr_dn (p-4) n ⊢ arr_dn p (n+1)` |
| `arr_up_cons`  | `(∃w, b ↦ₘ w) ∗ arr_up (b+4) n ⊢ arr_up b (n+1)` |
| `arr_up_uncons`| `arr_up b n ∗ n≠0 ⊢ (∃w, b ↦ₘ w) ∗ arr_up (b+4) (n-1)` |
| `arr_*_nil`    | `⊢ arr_* p 0` and `arr_* p 0 ⊢ emp` |

(pub variants add `secLeakvar w`.) Plus a no-wrap side condition per lemma,
exact form to be settled in Phase 1 (probably `n ≤ 2^30` and the address range
bound `gen_base_bound` already states).

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
          ∗ arr_dn priv (dp-4) c          -- sources not yet moved
          ∗ (∃w, dp ↦ₘ w)                 -- the destination of this trip
          ∗ arr_up priv (dp+4) k          -- already moved
          ∗ ⌜dp = e + 4c⌝ ∗ ⌜N = k + c⌝   -- tie the ghosts to the state
    post := S0 ↦ᵣ e ∗ T6 ↦ᵣ 0 ∗ (∃w, e ↦ₘ w) ∗ arr_up priv (e+4) N
          ∗ arr_dn priv (e-4) 0

Ghosts: `arr_dn_pop` before the `lw`; `arr_up_cons` after the `sw`.
The two pure facts are the ONLY place multiplication appears, and they are
pure: at the back edge they become residual bv obligations
(`dp-4 = e + 4(c-1)` from `dp = e + 4c`), discharged by `solve_vc`'s residual
tactics, not by peval. Open question for Phase 3 whether they need to be
stated over `unsigned` in `ty.int` to be lia-closable.

### D4. Binary interpretation

`arr_dn pub p n` := `[∗ list] i ∈ seq 0 (unsigned n), ∃ w, ptstomem (p - 4i) w`
(`w` SyncVal when `pub`), and `False` when the address or count is a
`NonSyncVal` -- the count must be public, which is exactly the property that
makes the loop cuttable at all (PLAN-muladd-composed §2).

## Relation to the previous machinery (Iris-level composition)

This is NOT a new decomposition. `GenCompose.v` already has it, at the Iris
level:

| GenCompose (LoopSpec route) | this plan (loop-block route) |
|---|---|
| `loop_reservoir A iota q n` (:1081), big-sep over `seq 0 n`: trips not reached | `arr_dn` |
| `loop_completed A iota q n N` (:1407), trips already run | `arr_up` |
| `Fr n := loop_reservoir … n ∗ loop_completed … n N` | D3's `inv` |
| `loop_reservoir_peel` / `loop_completed_push` | `arr_dn_pop` / `arr_up_cons` |
| the cell trade `Hc` (`loop_cells_trade`), a hand-written Iris proof per loop | done by the executor + solver |

**Why it cannot be reused as is.** The old route took its trip count from
the META-logic (`myWP2_loop_induction` inducts on a `nat n`), so the
size-dependent part could stay an `iProp` frame outside the executor, which
only ever saw one trip's fixed window. The loop-block route has no such `n`:
the invariant IS the contract's precondition, checked by one executor run,
with Löb as the induction. So the size-dependent part must live in the
executor's heap, i.e. be a CHUNK. And a chunk cannot be `loop_reservoir`
itself: that is parametric in an arbitrary `Assertion A`, and `Sig.v` sits
below the assertion language. Hence the specialisation to word arrays.

**What carries over.**
- **The soundness proofs.** D4 interprets the chunks as `big_sepL` over
  `seq`, exactly like `loop_reservoir`, so the `*_sound` lemmas are
  `loop_reservoir_peel` / `loop_completed_push` again (`seq_S`,
  `big_opL_app`, `big_sepL_cons`). Keep the interpretation in that shape ON
  PURPOSE.
- **§R11's vacuity lesson.** A reservoir whose cells overlap is `False`, so
  every lemma about it "proves" from an unsatisfiable premise. Same risk here:
  a count large enough to wrap the address space makes an array overlap
  itself. The lemma proofs stay sound, but an invariant could become
  unsatisfiable without any test noticing. Hence Phase 0's ENTRY CHECK below.
- **Gone:** the per-loop trade (the executor does it), and the across-trip
  disjointness criterion of §R11 (the three chunks of D3 are disjoint by
  construction, given no wrap).
- **Dissolved, not solved:** §R11's D blocker was a uniform width-2 window
  at every trip, whereas trip 0 touches one cell. With a count-indexed chunk,
  width is DATA, not shape, so the mismatch does not arise.

**What the old route had and this plan loses: generality.** `loop_reservoir`
takes ANY per-trip cell shape (several cells per trip, two bases, a public
and a private cell). `arr_*` are single-word, stride 4, one direction. That
covers D/I/K/M (I and K's two arrays become two chunks). Another stride or a
record-shaped cell would need a new predicate or a Coq-level stride
parameter. OPEN, see Q1.

## Open questions

- **Q1. Stride parameter** -- DECIDED yes, see A3.
- **Q2. Lemma preconditions must use `asn.chunk_angelic`.** Only
  `consume_chunk_angelic` (Monads.v:858) has the `heap_extractions` fallback;
  plain `consume_chunk` errors when neither exact nor precise matching
  succeeds. Split/join lemmas consume the ARRAY chunk first (the unique
  instance of its predicate, so no real choice), which binds the address;
  the neighbouring cell is then found PRECISELY (`a ± s`, a term, after peval).
- **Q3. INTRODUCING an array needs a term argument.** `⊢ arr p 0` (or
  `cell a ⊢ arr a 1`) has no array to match: its address is either an
  unconstrained angelic variable (which no later precise consume can equate
  with `dp`) or an angelic choice among ALL cells in the heap (ambiguous).
  Split/join never needs this, since every one of them consumes an existing
  array; only the CALLER-side conversion from concrete cells does (Phase 3).
  So Emiel's "ghost variable" suggestion is needed after all, for intro
  lemmas only: an annotation kind whose arguments are terms over the
  enclosing contract's logic context. Hence Phase 0's entry check moves to
  the Iris level (Phase 1: the interpretation at a concrete count is
  inhabited), and the ghost-variable annotation joins Phase 3.

## Files touched

| file | change | cost |
|---|---|---|
| `RiscvPmp/Sig.v` | two `Predicate` constructors, `𝑯_Ty`, precise, dup | forces the whole RiscvPmp rebuild |
| `RiscvPmp/IrisInstance.v`, `ModelBinary.v` | interpretation | |
| `RiscvPmp/Machine.v` | `Lem` constructors (ghost only; no FunDef uses them, program semantics unchanged; no leak token, so leakage-model-change's gate does not apply) | |
| `CFGVer/Spec.v` | `SepLemma`s + `LEnv` arms | light |
| `CFGVer/SpecIris.v` | `*_sound : ValidLemma …` | heavy |
| `RiscvPmp/Contracts.v`, `BinaryBlockVer/Spec.v` | `LEnv` arms, if their matches are exhaustive over `Lem` | check |

No `theories/` change. No executor change. No trusted-surface change
(Noninterference.v, `*Result.v` statements, `*_instrs`/`*_specs` untouched).

## Phases (each ends in a GATE: reach it, report, commit, stop)

- **0. Spike, light side only.** Predicates + lemma CONTRACTS (Sig.v,
  Machine.v, Spec.v); Iris interpretation stubbed only if the build forces it.
  Probe `Example/ZZArrD.v`: D standalone as an `ai_loop` block with D3's
  invariant, `solve_param_vc`. GATE: VC green AND two negative controls
  REJECTED (an invariant that drops `arr_up_cons`'s cell; a wrong `N`).
  The ENTRY CHECK (the invariant is satisfiable, not merely preserved:
  §R11's lesson) moved to Phase 1, at the Iris level, because building an
  array from concrete cells inside the executor needs Q3's term-argument
  annotation. Phase 0 adds all predicates and all split/join lemma
  contracts (count-indexed AND `arr_rng`) in ONE Sig.v/Machine.v pass.
  This settles A2 (does angelic matching resolve without branching?) and D3's
  residuals before any Iris work.
- **1. Interpretation + lemma soundness.** D4; `*_sound` in SpecIris.v.
  GATE: `make Results.vo` green; `Print Assumptions` of a lemma soundness
  proof axiom-clean.
- **2. D end-to-end standalone.** `ZZArrDResult.v` via `cfg_instrs_endToEnd`,
  like CountdownRecResult. GATE: axiom-clean end theorem.
- **3. D inside muladd.** The caller's side: converting muladd's concrete
  cells into `arr_*` chunks (at mlen=2, concrete counts: `arr_*_nil` then
  pushes, as ghosts in the preceding segment). Needs Q3's annotation kind
  (lemma arguments as terms over the contract's logic context: Verifier.v
  Annot, sexec/cexec/rexec ghost cases, sound_cexec_ghosts). GATE:
  `bc_run_in_muladd`-style run of D at idx 84.
- **4. K, then I, M.** Two arrays per loop, one private (x[]) and one public
  (m[]): different flags, so angelic matching still has one candidate per
  lemma. GATE per loop as Phase 0.

## Risks

- **Angelic ambiguity** (A2): two same-flag arrays in the heap give the
  consume an `angelic_list` choice per lemma call. Wrong choices should fail
  at the next load, but cost is unmeasured. Measure in Phase 0/4.
- **bv residuals** (D3): the ghost-tie facts may not close under the existing
  residual tactics; restating over `unsigned` is the known fallback.
- **peval on `(dp + -4) + 4`**: invariant re-establishment needs the cons'd
  address to fold back to `dp`; `try_bvadd_cancel_*` should do it -- check in
  Phase 0 before relying on it.
- **Rebuild cost**: Sig.v sits under everything RiscvPmp. Batch every Sig.v
  edit into one pass (GATE_JOBS=1 on this box).
