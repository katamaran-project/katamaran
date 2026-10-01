# PLAN — array invariants for loop blocks, 2026-09-28

Status: **rev 3, APPROVED 2026-09-28; Phase 0 next.** Nothing built.
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
- **A5. ONE predicate family, `arr pub s [a; n; e]`** (rev 3; replaces rev
  2's `arr_dn`/`arr_up`/`arr_rng`). Start address `a`, count `n`, end `e`.
  - Direction is not a separate family: the stride is a Coq-level `N` and
    addresses are modular, so a downward walk is stride `2^32 - 4`.
  - Count AND end in one chunk: the multiplicative relation `e = a + s·n` is
    stated ONLY in the Iris interpretation and proved once, in the generic view
    entailments -- never in a contract, never by the solver. (Rev 2's A5, a
    `ring` residual closer for `e = dp - s·c` ghost ties, is gone with it.)
  - Why keep the count (Emiel asked whether endpoints suffice): a
    COUNTER-driven loop (D: `addi T6,T6,-1 … bnez T6`) knows only `c ≠ 0`.
    With the count in the chunk the invariant shares the variable
    (`T6 ↦ᵣ c ∗ arr … (dp-4) c E`), so `c ≠ 0` IS non-emptiness. Endpoints
    only would put `dp - 4 - E = 4c` in the contract and leave the solver
    `dp-4 ≠ E` from `c ≠ 0` at every pop: a disequality under a symbolic
    multiplication, needing a no-wrap bound. POINTER-bounded loops (K, M)
    leave the count existential and pop on `a ≠ e`.

## Design

### D1. The predicate (Sig.v)

    arr pub s [a; n; e]   cells a, a+s, …, a+s(n-1);  e = a + s·n

All args `ty_xlenbits`; precise on `a` (input), `n` and `e` outputs, so a
consume matches by start address and the solver equates count and end. Not
duplicable. Two arrays with different flag or stride are different
predicates (the flag and stride are part of the `Predicate` index).

### D2. The ghost annotation (CFGVer-local, replaces Katamaran ghost lemmas)

A new `Annot` kind in `Verifier.v`, next to `AnnotLemmaInvocation`:

    AnnotView {Δ} (pre post : Assertion Δ)

"consume `pre`, produce `post`", with `Δ` bound angelically by the consume --
`call_lemma`'s shape without an `LEnv` entry and without patterns. The
executor trusts it on the light side; its VALIDITY (`∀ ι, interpret pre ι ⊢
interpret post ι`) rides in `AnnotInstrV` and is discharged on the heavy side,
exactly as block validity does (PLAN-valid-blk-annot). The views used below
are instances of a handful of GENERIC entailments, proved once.

Binding: `pre` consumes the ARRAY chunk first, with `asn.chunk_angelic` --
only `consume_chunk_angelic` (Monads.v:858) has the `heap_extractions`
fallback. The array is the only chunk of its predicate in the heap, so there
is no real choice, and it binds `a`/`n`/`e`; the neighbouring cell is then
consumed PRECISELY at `a ± s`, a term after peval.

| view | statement |
|---|---|
| `take_first` | `arr a n e ∗ n≠0 ⊢ cell a ∗ arr (a+s) (n-1) e` |
| `take_first'`| `arr a n e ∗ a≠e ⊢ cell a ∗ arr (a+s) (n-1) e` (pointer loops) |
| `add_first`  | `arr a n e ∗ cell (a-s) ⊢ arr (a-s) (n+1) e` |
| `take_last`  | `arr a n e ∗ n≠0 ⊢ arr a (n-1) (e-s) ∗ cell (e-s)` (+ `a≠e` variant) |
| `add_last`   | `arr a n e ∗ cell e ⊢ arr a (n+1) (e+s)` |
| `empty`      | `arr a 0 e ⊢ ⌜a = e⌝` |

`cell x` := `∃w, x ↦ₘ w` (plus `secLeakvar w` when `pub`), and every TAKE
also produces the taken cell's range fact `unsigned x + 4 ≤ maxAddr`: the
memory read/write contracts demand it and nothing else supplies it for a cell
of a symbolic array. So the interpretation carries the range (D4). Wrap: bv
arithmetic is modular, so the index shifts are ring identities; an `add`
whose count wraps to 0 has an `emp`-sized right-hand side (affine).

### D3. ACCUMULATOR invariant, not a recursive post

A recursive post ("all c+1 cells") needs a FOLD after the back edge's block
returns -- a ghost with no instruction to hang it on (the block resumes at the
loop's exit, outside its code), i.e. a new "ghost after firing" hook in the
executor + refinement + soundness. Avoided by the tail-recursive shape: the
written cells accumulate IN the invariant, the post is trip-invariant, and the
back edge passes it through unchanged.

Loop D (`lw S1,-4(S0); addi T6,T6,-1; addi S2,S0,-4; sw S1,0(S0); mv S0,S2;
bnez T6`), context `q` (code base), `dp`, `c`, `k`, `E`, `T`:

    inv  := S0 ↦ᵣ dp ∗ T6 ↦ᵣ c ∗ c≠0 (public: dp, c) ∗ (∃ S1, S2)
          ∗ arr priv (-4) (dp-4) c E      -- sources not yet moved, walking DOWN
          ∗ cell dp ∗ ⌜range dp⌝          -- the destination of this trip
          ∗ arr priv 4 (dp+4) k T         -- already moved
    post := ∃ f, S0 ↦ᵣ f ∗ T6 ↦ᵣ 0 ∗ cell f
          ∗ (∃ m, arr priv 4 (f+4) m T)
          ∗ arr priv (-4) (f-4) 0 E

`E`, `T` are the arrays' own far ends, constant across trips and fixed by
consuming the chunks; no ghost tie. Views: `take_first` (stride −4) before
the `lw`; `add_first` (stride 4) after the `sw`. The EMPTY source array stays
in the post as a chunk: the executor never learns `e = a + s·n`, so it could
not prove `f - 4 = E` at exit. A caller that wants that fact applies `empty`.

### D4. Binary interpretation

    arr pub s a n e := ⌜e = a + s·n⌝ ∗ ⌜every cell in range⌝
                     ∗ [∗ list] i ∈ seq 0 (unsigned n), ∃ w, ptstomem (a + s·i) w

(`w` SyncVal when `pub`); `False` when an address or the count is a
`NonSyncVal` -- the count must be public, which is exactly the property that
makes the loop cuttable at all (PLAN-muladd-composed §2).

## Relation to the previous machinery (Iris-level composition)

This is NOT a new decomposition. `GenCompose.v` already has it, at the Iris
level:

| GenCompose (LoopSpec route) | this plan (loop-block route) |
|---|---|
| `loop_reservoir A iota q n` (:1081), big-sep over `seq 0 n`: trips not reached | `arr` walking down (stride −4) |
| `loop_completed A iota q n N` (:1407), trips already run | `arr` walking up (stride 4) |
| `Fr n := loop_reservoir … n ∗ loop_completed … n N` | D3's `inv` |
| `loop_reservoir_peel` / `loop_completed_push` | `take_first` / `add_first` |
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
takes ANY per-trip cell shape. `arr` chunks are single-word cells at a Coq-level
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
| `RiscvPmp/Sig.v` | one `Predicate` constructor `arr (pub : bool) (s : N)`, `𝑯_Ty`, precise, dup | forces the whole RiscvPmp rebuild |
| `RiscvPmp/IrisInstance.v`, `ModelBinary.v` | interpretation | heavy |
| `CFGVer/Verifier.v` | `AnnotView` + its `sexec_ghost` arm | light |
| `CFGVer/VerifierRel.v` | `cexec_ghost` arm + refinement (pet cannot open this file: probe-file workflow) | heavy |
| `CFGVer/Adequacy.v` / `Validity.v` | view validity in `AnnotInstrV`/`annotsValid`, soundness of the ghost step | heavy |
| `CFGVer/GenCompose.v` (or a new heavy file) | the generic view entailments | heavy |

No `theories/` change. No `Machine.v` change. No trusted-surface change
(Noninterference.v, `*Result.v` statements, `*_instrs`/`*_specs` untouched).

## Phases (each ends in a GATE: reach it, report, commit, stop)

- **0. Spike, light side only.** the Sig.v predicate + `AnnotView` in Verifier.v with its symbolic arm; Iris side stubbed
  only if the build forces it. Probe `Example/ZZArrD.v`: D standalone as an
  `ai_loop` block with D3's invariant, `solve_param_vc`. GATE: VC green AND two negative controls REJECTED (an invariant
  that drops `add_first`'s cell; a wrong `N`). Settles D2's binding claim and
  the peval folding risk before any Iris work.
- **1. Interpretation, view entailments, ghost soundness.** D4; the generic
  entailments; `cexec`/`rexec` arms and the ghost step's soundness; view
  validity in the seal. GATE: `make Results.vo` green; ENTRY
  CHECK: the interpretation of D's `inv` at a concrete count is inhabited.
- **2. D end-to-end standalone.** `ZZArrDResult.v` via `cfg_instrs_endToEnd`,
  like CountdownRecResult. GATE: end theorem compiles (no routine
  Print Assumptions -- Emiel 2026-09-28; the merge hook's gate still runs it).
- **3. D inside muladd.** The caller's side: converting muladd's concrete
  cells into `arr` chunks (Q1's context-indexed views). GATE:
  `bc_run_in_muladd`-style run of D at idx 84.
- **4. K, then I, M**, popping on `a ≠ e`. Two arrays per loop, one private (x[])
  and one public (m[]): different flags, so each view still has one
  candidate. GATE per loop as Phase 0.

## Risks

- **Angelic ambiguity** (D2): two arrays with the same predicate, flag and
  stride give the consume an `angelic_list` choice per view. Wrong choices
  should fail at the next precise consume, but cost is unmeasured. Measure in
  Phase 0/4.
- **peval on `(dp + -4) + 4`**: invariant re-establishment needs the cons'd
  address to fold back to `dp`; `try_bvadd_cancel_*` should do it -- check in
  Phase 0 before relying on it.
- **Rebuild cost**: Sig.v sits under everything RiscvPmp. Batch every Sig.v
  edit into one pass (GATE_JOBS=1 on this box).
- **VerifierRel.v cannot be opened by pet**; the refinement arm for
  `AnnotView` needs the probe-file workflow the ghost-refinement work used.

## Progress log

### Phase 0 (2026-09-28, branch `issue/array-invariants`)

- **Sig.v**: `arr (pub : bool) (s : Z)`, args `[a; n; e]`, precise on `a`,
  not duplicable. The stride is a `Z`, not an `N`: `Derive EqDec` needs an
  `EqDec` instance per field and there is none for `N` (there is `Z_eqdec`),
  and a signed stride says "walks down" as `s = -4` directly.
- **Verifier.v**: `AnnotView {Δ} (pre post : Assertion Δ)`, executed as
  `call_lemma (MkLemma [ctx] _ [env] pre post) [env]`. `cext_sexec_ghost`
  needed a third case -- WITHOUT `cbn`, which unfolds `call_lemma` at the
  concrete `MkLemma` and defeats `apply cext_call_lemma`. Rebuild cost of the
  Sig.v edit to the light closure: 75 s (not the feared full rebuild).
- **Probe `Example/ZZArrD.v`** (untracked). First run: `take_first` fired as
  designed (array found angelically, cell `dp-4` and its range fact
  produced), `lw`/`addi`/`addi`/`sw` all executed; `add_first` FAILED.
- **Root cause: `peval_bvadd` was not canonical at zero.** Its two
  constant-folding clauses returned `bv.add v1 v2 ⊕ t'` even when the sum is
  0, so `(dp ⊕ 4) ⊕ -4` became `0 ⊕ dp`, while the direct clause turns
  `dp ⊕ 0` into `dp`: one address, two spellings, and the precise consume of
  the cell at `a - s` missed the heap's bare `dp`. Inherent to array views
  whenever a pointer register is itself a cell address, so not D-specific.
  FIXED in `theories/Symbolic/PartialEvaluation.v` (Emiel approved the
  theories/ change): helper `peval_bvadd_fold` (returns `t'` at zero) +
  `peval_bvadd_fold_sound`; `peval_bvadd_sound` gains one
  `etransitivity; [apply peval_bvadd_fold_sound|]` step.
- **Process note**: the Sig.v/Verifier.v edits were first made through a
  Bash heredoc, which `skill-path-guard.sh` (Write|Edit only) does not see,
  so `cfgver-executor`/`cfgver-contracts` were loaded only afterwards.
- **GATE 0 MET.** After the rebuild (theories/ + all 18 tracked light
  examples, 55 files, 21:00, peak 5.3 GB, all green -- so no existing VC
  depended on the old `0 ⊕ x` spelling), `valid_d_rec` closes with
  `intros; vm_compute; solve_vc` in 154 ms; the whole probe compiles with
  coqc in 19 s. NO residual obligations: the pointer/count tie never reaches
  the VC. THREE negative controls, all REJECTED: (1) invariant without the
  destination cell, (2) post claiming T6 = 1 at exit, (3) invariant with an
  extra `c ≠ 1`, which the back edge cannot re-establish -- so the back edge
  really consumes the invariant through the block.
- Not yet shown: that the invariant is SATISFIABLE (Phase 1's entry check),
  and nothing is sound yet -- the views are trusted until Phase 1.

### Phase 1 (2026-09-28) -- GATE 1 MET

- **Design change (Emiel):** the anonymous `AnnotView pre post` became a
  CLOSED CATALOGUE `Verifier.CLem` (`clem_arr_take_first pub s`,
  `clem_arr_add_first pub s`) with `clem_lemma : CLem -> Lemma [ctx]`, and
  `Annot`'s constructor is `AnnotCLemma k`. Each entry is proved valid ONCE
  (`SpecIris.clemSem`), exactly as `lemSemCFGVerif` does for `LEnv`, so no
  validity premise is threaded through the soundness chain or the seal --
  Q2 is moot.
- **`add_first` now REQUIRES the new cell's range fact**
  (`Verifier.clem_range`): every arr cell carries one in the interpretation,
  so an add must be given it. D's VC still closes (its invariant states
  `range dp`).
- **Interpretation** (`IrisInstanceBinary.interp_arr`/`interp_arr_cell`) as
  D4. **Step lemmas** `interp_arr_take_first` / `interp_arr_add_first`
  (SpecIris, Section CLemSound): big_sepL cons + `fmap_S_seq`, index shift
  and end fact by `ring` at `bv xlenbits` -- stated as separate lemmas and
  APPLIED, because `ring` refuses a goal whose carrier spells the width
  unfolded. A count that wraps to 0 on `add` drops the cells (affine); the
  end fact still holds since then n = -1.
- **Entry check** `interp_arr_intro`: k concrete in-range cells ARE an arr
  of count k (for k < 2^32), so arr invariants are satisfiable.
- `cexec_ghost` arm (VerifierRel), `sound_cexec_ghosts` case (Adequacy);
  `rexec_ghosts`'s `destruct a; cbn; rsolve` closed the new case UNCHANGED.
- **Build:** SpecIris+VerifierRel 3:20 (7.1 GB), Adequacy 1:17 (6.9 GB),
  TablesRel..GenCompose 2:13, Results.vo incl. all examples 13:19 (8.0 GB);
  `scripts/gate.sh` PASSED (19 end theorems axiom-clean). A first attempt at
  the whole chain in the background was reaped for low memory while the
  session was idle: build in foreground pieces, close pet first.
- **Traps:** `rewrite … by …` fails to parse under Iris's ssreflect `by`
  (use `; [|tac]`); a preamble needs `From Coq Require Import Lia` or `lia`
  is a syntax error; `destruct_syminstance` does not see through a named
  `LCtx` (`cbv [clem_ctx] in ι` first); `cbn -[interp_arr]` is the right
  unfolding before applying a step lemma (plain `cbn` unfolds `bv.bin`).

### Phase 2 (2026-10-02) -- GATE 2 MET

`Example/ZZArrDResult.v` (untracked probe, with `Example/ZZArrD.v`):
**`d_noninterferent`** -- `noninterferent_strong init_addr d_instrs
(init_addr+24) (d_reg_specs init_addr) (d_mem_specs init_addr)` for every
`init_addr` with `init_addr + 36 < lenAddr`. muladd's loop D alone, 2 trips,
over 3 private data cells right after the code; S0 pinned to the top cell
(`init_addr+32`) and T6 to 2, both public; S1/S2 free. coqc 39.6 s, 6.9 GB.

- `dRecBlk_valid` is ONE `exact (blkValid_of_seg … valid_d_rec)`: the loop
  block, catalogue ghosts included, is valid through the existing Löb door --
  so `sound_cexec_ghosts`'s AnnotCLemma case and `clemSem` are exercised for
  real.
- `dLink` (light): the whole program starting AT the loop, the block an
  ordinary `ai_block`, exits at +24; `valid_d_link` by `solve_param_vc`.
- ImplPre builds the invariant's arrays from the trusted statement's
  concrete cells AT THE IRIS LEVEL (`d_src_arr` via `interp_arr_intro`,
  `d_moved_arr` empty) -- so a WHOLE-PROGRAM entry needs no Q1 annotation;
  Q1 matters only for an array introduced MID-program (Phase 3).
- Address arithmetic trick: `of_N (ia + c) = of_N ia + of_N c` (`d_split`),
  reassociate, and the closed constant part closes by `f_equal`
  (computation). `N.of_nat 2 < bv.exp2 xlenbits`: `vm_compute; reflexivity`,
  not lia. `gen_implpre` leaves two shelved `?ι`s for pinned registers;
  `Unshelve. exact [ctx]. exact …` (any valuation).
- No routine Print Assumptions (Emiel); no Admitted in the file.

### Phase 4 (2026-10-02) -- GATE 4 MET for K, M and I

All three pointer-bounded sliding loops verify as ONE `ai_loop` block each,
at a SYMBOLIC trip count, by `solve_param_vc` alone (no residuals), each with
three negative controls REJECTED (a false post; an invariant the back edge
cannot preserve -- done count pinned to 0; the head without the `nonempty`
ghost). Untracked probes, all coqc-green:

| loop | probe | instrs | latch | coqc (VC + controls) |
|---|---|---|---|---|
| K `br_i31_add` | `Example/ZZArrK.v` | 13 | `bne T5, S0` (m ptr) | 42.8 s |
| M `br_i31_sub` | `Example/ZZArrM.v` | 13 | `bne A4, A2` (m ptr) | 39.2 s |
| I limb mul-acc | `Example/ZZArrI.v` | 29 | `bne A1, T1` (x ptr) | 110.0 s |

(K's VC alone: 772 ms interactively.)  I contains MUL/MULHU and an SLTU
carry on private data -- no residual.

- **One new catalogue entry, `clem_arr_nonempty pub s`**
  (`arr a n e ∗ a≠e ⊢ arr a n e ∗ n≠0`; soundness `clem_nonempty_sound`,
  from the end fact with n = 0). It turns the pointer latch into the count
  fact `take_first` needs; the two REMAINING arrays share the count `n`, so
  one call covers both.
- **No `add_last` needed** (the plan's D2 listed it): the DONE arrays walk
  DOWN from the pointers (stride −4), so each trip adds at their FRONT with
  the existing `add_first`, and `(ap−4)+4` folds back to `ap` (the Phase-0
  peval fix). This also makes K's four arrays FOUR DISTINCT PREDICATES
  (pub × stride), so every angelic ghost call has exactly one candidate --
  the ambiguity risk of D2 never arises.
- Invariant shape for all three: pointer registers (public) ∗ the latch
  disequality ∗ scratch registers ∗ remaining-m `(true,4) [bp;n;·]` ∗
  remaining-x `(false,4) [ap;n;·]` ∗ m-done `(true,−4) [bp−4;k;mE]` ∗ x-done
  `(false,−4) [ap−4;k;xE]`; ghosts `nonempty; take_first x; take_first m`
  at the head and `add_first x-done; add_first m-done` after the store. M and
  I were GENERATED from K's file by register/instruction substitution.
- Heavy chain past SpecIris.vo NOT rebuilt since `clem_arr_nonempty` (no
  heavy edits expected: `sound_cexec_ghosts` uses `clemSem k` generically).

### Phase 3 SPIKE (2026-10-02) -- route (A) WORKS, no new machinery

Emiel chose: spike route (A) (angelic seed), fall back to (B) (named-term
lemma arguments) only if it branches badly. It does not.

- **Two new catalogue entries** (Verifier.v, proved in SpecIris, `clemSem`
  now 5 cases): `clem_arr_empty pub s` (`secLeak a ⊢ arr a 0 a`, `a`
  UNCONSTRAINED -- a seed) and `clem_arr_add_last pub s`
  (`arr a n e ∗ cell e ∗ range e ⊢ arr a (n+1) (e+s)`, the cell matched with
  `chunk_angelic`, which is what binds a fresh seed's address).
- **Probe `Example/ZZArrDEntry.v`** (untracked): a NOP whose ghosts_after
  build D's arrays from individual cells (two seeds, two add_last), then D's
  loop as an ordinary `ai_block`. Its precondition holds D's three cells and
  TWO DECOY cells at an unrelated base, so the first add_last's angelic cell
  choice is genuinely 5-way. `valid_e`: `solve_vc` in 177 ms; the file
  (incl. D's angelic-moved-array variant `valid_d_recA` and three controls:
  one add_last too few, the dp-4 cell missing, T6 pinned to 3 -- all
  REJECTED) compiles in 23 s.
- **Why it is cheap:** the ghosts sit on the instruction RIGHT BEFORE the
  block, so a wrong angelic choice fails one step later, at the block's
  precondition, and is pruned; and the seed's address is substituted
  EAGERLY once bound, so every later add_last is a precise, deterministic
  match. Only the first choice per array branches.
- **The one design cost:** an array that starts EMPTY at a block's entry
  (D's moved array) must be matched with `chunk_angelic` in the block's
  precondition, so the unconstrained seed can be bound by the match.
- **Soundness finding:** `⊢ arr a 0 a` alone is NOT a valid lemma --
  `ValidLemma` quantifies over every valuation and `arr` is False at a
  NonSyncVal address. The seed needs `secLeak a` in its precondition. Found
  by writing the soundness proof; the executor trusts catalogue entries, so
  no VC could have caught it. Rule: a new catalogue entry is not usable
  until its ValidLemma is proved.
- Heavy chain past SpecIris.vo still not rebuilt (no heavy edits).

### Toward the flat muladd with loop blocks (2026-10-02, in progress)

Probe `Example/ZZMuladdBlk.v` (untracked): ZZMuladdFullN2's instructions and
contract (copied -- that file is on the pre-`cfg_init_addr`-removal API and
Requiring it would run its OOM flat VC), with deviation 3 REVERTED (both
`li _, 32` restored, since loop blocks make the trip count irrelevant).

- **All five loops verify as blocks** (probes ZZArrD/G/I/K/M.v, each with
  three rejected controls). G added as `Example/ZZArrG.v` (register-only,
  18.5 s). Code-equality lemmas `mb_{d,g,i,k,m}_code` pin each block's code
  to muladd's own instructions at idx 84/135/190/237/264 (reflexivity).
- **Step A (only G as a block): OOM at 9.4 GB after 71 s.** Cause is known
  (diagnostics/muladd-full-cost-drivers.md): I's carry-chain term
  duplication runs inside the flat VC unless I is a block too.
- **Contracts made CALLER-READY** (all probes re-verified): posts hand back
  the scratch registers the precondition consumed (else they are dropped
  and code after the loop cannot read them); arrays EMPTY at entry (done
  arrays, D's moved array) matched with `chunk_angelic`.
- **Exit side needed three things** (probe `Example/ZZArrDExit.v`, cells ->
  arrays -> D block -> cells, by `solve_param_vc`, control rejected):
  1. `clem_arr_empty_elim` (`arr a 0 e ⊢ a = e`) so a caller learns an
     existential exit pointer; it works only if the post names the pointer
     BARE as an array start -- the solver substitutes `g = E` but NOT
     `c + f = t` (found by reading the debug VC: cells stayed at `f`).
  2. `clem_arr_lockstep` (same stride + same count: one start = end gives
     the other) for K/I/M's NON-latch pointer; posts restated with the latch
     pointer as its end `e` and the other bound bare by its remaining array.
  3. residual closers `relval_neq_offset(s)` (Contracts.v, in
     `solve_symbase_fetch`) for `x ≠ c + x` / `c1 + x ≠ c2 + x`, left by
     `nonempty` on arrays over one base.
  Plus `clem_arr_drop` to remove spent arrays. `clemSem` covers 8 entries.
- **Step B (all five loops as blocks + conversion ghosts): OOM at 8.1 GB
  after 436 s** (vs 71 s) -- the loop bodies left the VC, something else is
  still too big. **Prefix probes** `Example/ZZMbPre{83,90,91,...}.v`:
  - prefix 83 (before D): verifies, **4.4 s**, 4.6 GB.
  - prefix 90 (D's build ghosts + D block): verifies, **84.5 s** -- D's
    ENTRY costs ~80 s. Working hypothesis: angelic `heap_extractions`
    search over a ~130-chunk heap (instruction words, registers, cells) at
    every angelic array/cell match; unmeasured.
  - prefix 91 (+ D's split + one instruction): FAILS (not yet diagnosed).
- **Tried and reverted:** `arr` precise on NO inputs (so ghost lemmas match
  by predicate, no heap search). Sound, but a block precondition then no
  longer rejects a wrongly seeded array by address syntax: it asserts the
  address equation, which is satisfiable for a cell at an unrelated base,
  so the wrong branch survives as an unresolved angelic disjunction
  (ZZArrDEntry's decoys). Ghost lemmas want "by predicate", block
  preconditions want "by address".

### 2026-09-29 -- THE FLAT MULADD VERIFIES (light-side VC)

`Example/ZZMuladdBlk.v`: `valid_mb : cfg_vc mb_contract mb_annot` --
br_i31_muladd_small whole-function, mlen = 2, clang's own instructions with
deviation 3 reverted (both `li _, 32`), all five loops as blocks with the
conversion ghosts around D/I/K/M. **VC 126 s, whole file 282 s, peak RSS
8.5 GB** (needs a >11.5 GB virtual cap: the Qed's VM re-check).

Two fixes got it there, neither array-specific:
1. **Precise chunk matching compares the heap chunk's inputs NORMALISED**
   (theories/Syntax/Chunks.v, commit c32d2d6b). A heap term holding a
   variable substituted after the chunk was produced is not re-peval'd
   (`4 + g`, g := 0x468 + p, stays `4 + (0x468 + p)`); the consumed chunk
   is (`0x46c + p`), so a STORE (exact address match) missed the cell.
   Reads hid it: they fall back to an angelic match. Prefix 91 failed on it.
2. **solve_vc no longer calls `solve_bv`** (Contracts.v). The name resolves
   to theories/Bitvector.v's `Tactic Notation "solve_bv" := bv.bv_zify`
   (a tactic notation beats an Ltac), so every VC goal got the full bv
   decision procedure: 77 of 79 s per prefix. All 18 tracked examples
   verify without it.

**My angelic-heap-search hypothesis for D's 80 s entry was REFUTED by the
ablation**: `vm_compute` (the executor) was 3.5-4.5 s with or without the
ghosts; the cost was entirely in the tactic. Prefix timings after both
fixes: 90 -> 7.1 s, 163 (through G) 9.9 s, 220 (through I) 53 s / 7.0 GB,
251 (through K) 89 s / 8.2 GB, full 126 s / 8.5 GB.

Still open: (1) this is `cfg_vc`, not yet `ValidCFGVerifierContract` --
needs `blkValid` for the five loop blocks (heavy, via `blkValid_of_seg`, as
ZZArrDResult does for D) and `annotsValid` for the annotated list; (2) the
end theorem (`noninterferent_strong` through the memory bridge, ImplPre
over mlad's reg/mem specs); (3) heavy chain not rebuilt since the Chunks.v
fix; gate before merging; (4) the probes are untracked.

### 2026-09-29 (later): END TO END

**`mb_noninterferent` is proved** (`Example/ZZMuladdBlkResult.v`, untracked
probe): `noninterferent_strong` for the flat muladd (mlen=2, all five loops as
blocks), axiom-clean (pure_decode, mmioenv). File 43 s / 7.2 GB; it reuses
`valid_mb` from the light `.vo`. Three pieces:
1. **The seal's witness is TYPED** (commit a8367495, Emiel's call): 
   `ValidCFGVerifierContract c := ∃ LV : list (AnnotInstrV blkValid),
   cfg_vc c (map (eraseV c) LV) ∧ map aiv_instr LV = cfg_instrs c ∧ no aiv_loop`.
   Blocks carry their blkValid proof; `annotsValid` is no longer proved by
   anyone (it survives only inside `_elim`). Results.vo green (634 s).
2. **Loop blocks valid by conversion**: `blkValid_of_seg … (map liftV
   (x_annot_with xRecBlk)) … valid_x_rec` -- `liftV` (block-free annotation
   -> typed list) erases back to the source list definitionally, so each
   loop's existing VC is reused unchanged (10 ms each).
3. **`gen_contract_noninterferent_rel` restored** (5a5ad48b): the contract
   must stay unclassed (entry ghosts build arrays from single cells), and
   that bridge had been deleted as callerless on 2026-08-18.

Still open: gate before merging (heavy chain now rebuilt, Results.vo green);
the probes are untracked -- promoting ZZMuladdBlk{,Result}.v and the ZZArr*
loops means naming them and adding them to _CoqProject + AXIOM_CLEAN_THMS.

## PARAMETRIC mlen (2026-09-29, Emiel: "make it parametric")

Goal: `∀ mlen` (bounded) muladd noninterference from ONE symbolic VC; the
statement is a Coq-level ∀ over spec lists generated from mlen, so
Noninterference.v is untouched.  Probes (untracked): ZZMbSym1/2/3/3n.v,
ZZMbArith.v, ZZArrDAng.v.

**Prefix through loop D VERIFIES at symbolic mlen** (`ZZMbSym3.valid_sym3`,
Qed, file 36 s / 4.8 GB; negative control ZZMbSym3n -- wrong array count --
FAILS at the closer).  What it took:
1. m[0] = b symbolic public.  Early returns and the "mlen = 1" branch are
   refuted by stating the code's OWN branch conditions in the precondition
   (`sext b <> 0`, `31 <u sext b`, `((-1+M) & 0x3fffffff) <> 0`), plus an
   upper bound `sext b <u 65536` (else 31 + b wraps).  `sext` at equal width
   is not peval'd away (candidate peval rule; `sext_id32` closes it here).
   mblr = 0 is a public fork; pruned in the spike, both paths needed for real.
2. Addresses at the code's own terms: x[mlen] at `x + (M<<2)`, x[mlen-1] at
   `x + ((-1+M)<<2)`, x[mlen-2..1] an arr; `asn_in_range` of those exact
   terms closes the data bounds syntactically.  `x` stays a FREE public
   variable: the layout is only the end-to-end bridge's business.
3. THE WALL: the code names one address two ways -- index 74 uses
   `(-1+M)`, D's count is the MASKED `C = (-1+M) & 0x3fffffff`.  Fix (b):
   D's entry chunks (source arr, dest cell) are `chunk_angelic`
   (ZZArrDAng.dAngRec; its own loop VC still closes, 0.18 s), so the
   mismatch becomes asserted equalities under an angelic choice over
   candidates.  A ghost lemma cannot help: the executor uses equalities
   only in solved form, and catalogue lemmas take no term arguments.
4. The closer (in ZZMbSym3, to be promoted next to solve_symbase_fetch):
   `left` (the right candidate is first), `cbn -[Erasure.inst_symprop]`
   (a bare cbn blows 7.6 GB -- the 2880-bit word binder), destruct the
   public b/x, read b's bounds off the `bv.ult` hypotheses, then rewrite
   with RelVal-level lemmas whose LHS IS the residual shape
   (`rv_mlen_mask`, `rv_shl_pred_addr`, `rv_bvadd_comm`) over bv lemmas
   proved in preamble mode (`mlen_mask`, `shl_pred_addr`, `sext_id32`).
   SSReflect rewrite is in scope: no `rewrite .. by`, use bullets.
Tooling: pet cannot hold these probes (7.6 GB cap); iterate with coqc
(~20-35 s/run).  A deliberately WRONG post hides all residuals: its error
absorbs every branch -- use a trivially true post when reading residuals.
Next: both mblr paths; the rest of the program (I/K/M entries angelic, G is
size-free); promote the closer; the ∀-mlen bridge (cells -> arr via
interp_arr_intro, generic HDataAddrs).

### 2026-09-29 (later): mblr = 0 covered (Emiel), generic closer

- Emiel chose to cover BOTH mblr paths (mblr = bitlen mod 31 = bits used in
  m's top word; the mblr = 0 path is legal, rare: bitlen a multiple of 31).
  That path has its own memmove (idx 113-117), a POINTER-compare loop:
  `ZZArrD0.v` (d0Rec), loop VC proved.
- D's parametric variant (`ZZArrDAng`) now builds its MOVED array walking
  DOWN (fixed start = first destination = x[mlen], grown at its end by
  add_last): the code reads x[mlen], x[mlen-1] right after the memmove and
  the catalogue has no take_last.
- Family needs mlen >= 3: after D the read of x[mlen-1] hits the moved array
  for mlen >= 3 but the x[1] cell for mlen = 2 -- a heap-shape split with no
  code branch.  (mlen = 2 is mb_noninterferent already.)
- GENERIC CLOSER `ZZMbClose.solve_mb_vc`: walks the inst_symprop ∧/∨/∀ tree
  (both sides of every angelic choice), leaves by `bv_lin` = bitvectors ->
  Z via unsigned (add/shiftl/shiftr/land-ones/same-width sext), variable
  bounds, `Z.to_euclidean_division_equations; lia`.  Closes D (3.8 s), D0
  (5.0 s) and the prefix through D (valid_sym3, 22 s); negative control
  still fails.  The hand lemmas (ZZMbArith) are superseded.

### 2026-09-29 (later): BOTH mblr paths verify to the merge (idx 123)

- `ZZMbSym4.valid_sym4 : cfg_vc sym4 sym4_annot` by `solve_mb_vc`: 101 s
  (VC generation ~17 s of it), 6.0 GB.  Negative control `ZZMbSym4n`
  (x array one limb short, mirroring ZZMbSym3n) fails, as it should.
- What it took, in order:
  1. Before: the closer ran 300-490 s and failed.  Cause: one address, two
     spellings (`(x + ((M-1)<<2)) + 4` vs `x + (M<<2)`), so reads missed
     their cell and fell back to an angelic disjunction over every cell.
     FIX (Emiel: "two peval rules"): `peval_bvadd_float` + `peval_shiftl`
     in `theories/Symbolic/PartialEvaluation.v`, commit 23f904fa; full
     Results.vo closure green, every existing example unchanged.
  2. D and D0 bind their pointer from the SOURCE array (`dp` = source
     start, registers checked after), so the loops never hand the caller's
     masked spelling back.  Loop VCs still close (4.4 s / 5.4 s).
  3. The D0 entry then left an ∃ the executor could not eliminate: its
     equation is `SyncVal a = c + ?dp`, not `?dp = t`.  `mb_search` gained
     an ∃ case: cbn, destruct public RelVals, `eexists`, split, fix each
     evar from its defining equation (`rv_bvadd_solve`, witness constant
     vm_computed so it is a literal, else `bv_lin` sees `bv.negate`), then
     the ordinary search.
- Next: the rest of the program at symbolic mlen (G, I, K, M entries), the
  whole-program VC, then the ∀-mlen bridge.

### 2026-10-01: the n-only tail VERIFIES; replay + public-zero rule (a1eb199a)

- ZZ chain rebuilt on the committed framework.  Two template fixes in
  `ZZArrLoopN.v`, both found by the rebuild, neither by the 09-30 runs:
  1. `secLeakvar "n"` in the invariant.  With the chunk-facts hook reverted
     nothing says the count is public (interp_arr forces it, the executor
     cannot know; IrisInstanceBinary.interp_arr's comment, 8015df3e).  IN
     failed without it.  The 09-30 "I/K/M pass" was measured WITH the hook
     live, so PLAN-chunk-facts' "pass without the hook" is wrong for IN.
  2. The post's done count is EXACT (`k + n`), no fresh `∃ c1`, and the
     invariant carries `secLeak k`, `k <u 2^30`, `k + n <u 2^30` (no wrap,
     so k + n is nonzero and is the next loop's bound).  With `∃ c1` the
     next loop's count was unconstrained: 18 closer leaves, 2 x 9, all about
     one variable, named "c1" (probe ZZMbTailND3).  So the n-only tail had
     NEVER verified: ZZMbTailT/U5's staged rig ran each stage as its own
     sentence, i.e. on goal 1 of 10 only (U5's "closer 10 s" is that).
- `valid_tail` (ZZMbTailNP, staged, real Qed), user time:

  | | vm_compute | solve_vc | goals | closer | Qed | file | RSS |
  |---|---|---|---|---|---|---|---|
  | before | 211.4 | 47.4 | 10 | 267.7 | 239.6 | 776 | 9.11 GB |
  | after a1eb199a | 143.6 | 36.5 | 8 | 170.1 | 150.0 | 508 | 9.14 GB |

  Construction is ALL executor: raw tree 11,130 nodes -> 141 after
  postprocess (+1.5 s); ~1,640 angelic binders, 99.4% eliminated at
  creation (register reads rs/reg_val 197 each, fetch/decode ~83 each, pc
  85 each), 10 survive to the closer; 3,622 angelic + 3,189 demonic binary
  nodes pruned (ZZTailExist, ZZTailCost{Raw,PP}).  Census (ZZMbTailNCensus):
  20 leaves, 10 ring identities substituted AFTER postprocess -> replay; 4
  `t + 0*M = t` -> drop_pub_zero.  Qed ~ re-runs the VM cast.
- Open: what in the executor's per-node cost (19 ms/node) dominates;
  the remaining leaves (range facts on M, a shift identity, secLeak of an
  evar); peak RSS (closer + Qed); Sym4/Sym6 on D0N.
