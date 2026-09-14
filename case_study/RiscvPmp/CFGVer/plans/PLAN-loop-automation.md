# PLAN — loop automation: get the specification right, apply one lemma

Target: once the SPECIFICATION is written, obtaining a loop's contract and
composing it with its neighbours is an application of a lemma plus a tactic,
with no hand-written glue.

Written 2026-09-13, after `loop_runs` / `loop_back_edge_std` / `loop_latch_obligation` /
`loop_completed` landed (commits 0568430f, e6cd34fc, 554f7cc7) and the composition
interface was read off an unfolded `mulinner_invariant`.

---

## 0. What is irreducibly SPECIFICATION

These have no canonical answer and must be written by a human.

1. **Publicness.** Which registers and cells are `secLeak`. This IS the
   security property; nothing derives it.
2. **Footprint ownership.** That the caller owns `[p, p+4n)`. An API contract;
   the code merely dereferences.
3. **The OUTERMOST postconditions.** What the whole program promises. Note the
   narrowing (2026-09-13, after review): an INTERMEDIATE cut assertion is NOT
   free — it is determined up to strengthening by its successor's
   precondition. Only the endpoints of a chain are genuine specification. This
   entry originally read "the exit postcondition", which over-claimed; see F2.

Everything else below is derivable, and the rest of this plan is how.

**Scope limit, stated up front:** `LoopSpec` is an AFFINE-INDUCTION-VARIABLE
abstraction. `iota : nat -> Valuation R` presupposes a closed form for every
variable at trip `n`. A linked-list walk (`p := p->next`), a data-dependent
index, or a variable stride falls outside it — there the pointer at trip `n` is
determined by the heap, not by `n`, and the representation itself must change
(`loop_reservoir`'s `[∗ list] i ∈ seq 0 n` becomes a recursive list-segment
predicate, and the per-trip obligation becomes "unfold one step"). That is a
different development, not a harder instance of this one. Nothing in this plan
attempts it.

---

## Phase A — record hygiene (cheap; unblocks the rest)

**A1. `cfg_exits` and `cfg_exitCond` are one datum stored twice.**
```
exits_of_offs p offs = map (fun o => peval_bvadd (of_N o) p) offs
seg_exitCond ia offs = fun v => orb over (bv.eqb v (of_N (ia + t)))
```
Both are functions of `offs : list N` and the two bases the record ALREADY
holds (`cfg_placement`, `cfg_init_addr`). Replace both fields with
`cfg_exit_offs : list N` and derive. Every call site in the tree already goes
through these two generators (one hand-rolled `fun v =>` found), so nothing is
load-bearing. **Payoff beyond tidiness:** storing both lets them drift, and the
soundness bridge currently has to PROVE they agree (`seg_exit_table_ok`,
`etable_rel`). Deriving makes that obligation vanish by construction.

**A2. `extend_to_minimal_post`.** `CFG_VC_triple` wraps the PRE in
`extend_to_minimal_pre`; the POST is wrapped by hand in each generator as
`(post ∗ minimal_pre)`. GenSegment's own comment records the failure mode when
a generator forgets: the post consumes `cur_privilege`/`inv_leakage`, so the
body runs exactly once, failing late and confusingly. Make it structural.
*Measure*: this puts `minimal_pre` into every VC uniformly, paid at
`vm_compute` scale on ~30 examples. Expected nil, not free.

**A3. `loop_final_contract` should BE an ordinary segment.** It composes today
(`loop_final_trip` is `seg_run_single_exit` underneath) but cannot be STATED in ordinary-segment
vocabulary, because `gen_loop_contract` forces the pre to `gen_loop_state ∗
guard`. Restate:
```
loop_final_contract ls post := gen_seg_contract ... (extra_pre := gen_loop_state ls ∗ exit-guard) post
```
Then `loop_final_trip` collapses into `seg_run_single_exit`, and `loop_body_trip`/`loop_final_trip` become
one lemma parameterised by the guard and the target.

**A4. Try moving `gen_pures` into `extra_an`.** Every edge proof has an `Hf`
bullet re-proving facts (`p1 ≠ p7`, range facts) that the post drops. They are
CONSEQUENCES of the previous trip plus the walk, not free choices, so the
executor could discharge them at the end of the body and `Hf` would disappear.
*Risk*: moves a one-line `lia` into the VC. Measure before adopting.

---

## Phase B — give DATA the base/offset treatment CODE already has

**RE-SCOPED 2026-09-13 by spike (b); the premise below was wrong.** This
section used to open by claiming data is not addressed base-relatively. It is:
`mem_spec_rel : N * bool * param_val` (address = `p + k`) has existed since the
unify-generators work and is cmovznz4's *production* path — its end theorem is
stated over `map (concretize_mem init_addr) cmovznz4_mem_specs_rel`. The
paragraph that follows is retained only because the *shape* of the complaint
survives: there are still two vocabularies, just not the two named.

What is actually true: `mem_spec_rel` is relative to the ONE distinguished base
`"p"` (the code base), with an `N` offset; `cell_spec` is relative to an
ARBITRARY variable `cell_base_var ∈ Σ` with a `bv` offset. So data can be addressed
relative to the CODE, but not relative to an independent data base. cmovznz4
gets away with one base because its data lives at `p+116 … p+160`, inside the
code image's tail.

And the binding constraint is not the vocabulary at all — see §Spike results
(b). It is `HDataAddrs`, a PLACEMENT premise carried by every EndToEnd bridge.

**B1 (cheap, ~25 sites, no soundness-chain impact).** Generalise `mem_spec_rel`
from the implicit `"p"` to a NAMED base, converging on `cell_spec`'s
vocabulary. The single-base assumption is confined to `GenContract.v` (22),
`EndToEnd.v` (2) and `GenCompose.v` (1); `Verifier`, `VerifierRel`, `Adequacy`,
`Spec`, `SpecIris`, `Tables`, `TablesRel` contain ZERO — the soundness chain is
already generic in Σ. Verified to restate an end theorem without loss: see
`Example/ZZSpikeMemBase.v`.

**B1' (expensive, HEAVY chain — the actual blocker).** Lift `HDataAddrs` and
`Adequacy.v`'s `instrsAndDataMemory` from ONE contiguous data run immediately
after the code to k disjoint runs. Today that lemma splits `liveAddrs` four
ways (`before ++ instrs ++ data ++ rest`) and inducts over one contiguous run;
k runs needs ordering/disjointness hypotheses between the bases. **B1 alone
buys nothing** — do not do it without committing to B1'.

**B2.** The bridging lemma: whole-program memory precondition ⊢ `loop_reservoir` /
`loop_completed` blocks. `loop_reservoir_words` and `mem_word` are the loop-side half and
already exist; B1 supplies the other half. This is what makes an array
expressible end to end.

**B3.** Consequence to check, not assume: a `CFGVerifierContract`'s post is an
`Assertion Σ` over a FIXED `Σ`, so it can never mention `n` cells. The reservoir
must therefore still be threaded as `seg_run_single_exit`'s opaque `iProp` frame. B1/B2
make the ENDPOINTS expressible; they do not remove that constraint.

---

## Phase C — derive the mechanical LoopSpec fields

**C1. Placement and control flow** — `loop_first_instr`, `loop_num_instrs`, `loop_exit_off`,
`loop_guard`, `loop_exit_guard`, `loop_fuel`. All computable from the instruction list: a
CFG pass finds the back edge and the fall-through, decode gives the branch
relop, fuel is the step count plus slack. Deliver as a Gallina function
returning a `LoopSpec` skeleton, with well-formedness `vm_compute`-checkable.

**C2. `iota` from induction-variable analysis.** **DOWNGRADED 2026-09-13 by
spike (a): this is a PROJECTION, not an analysis.** It used to be billed as
"THE big one" and as the largest single piece of real work in the plan; that
was wrong. Every stride is already DATA in the `LoopSpec` (`−loop_counter_step` for the
counter's variable, `−walk_step` for each `walk_reg`'s, 0 for everything else in
`R`), and the counter's anchor is the unique solution of `loop_latch_obligation`. No
instruction-level analysis is needed to produce `iota` for any loop already
expressible as a `LoopSpec`. What stays free is one anchor per NON-counter
walking pointer — exactly the datum a predecessor segment supplies, so it is an
input by design, not a gap. `Hk`, `Hkn`, `Hw`, most of `P` and the affine part
of the cell trade still hang off it; they just cost less than budgeted.
Evidence: §Spike results (a), 7/7.

**C3. Derive the trip predicate `P`.** It must imply exactly: the no-wrap
bounds the latch needs, the address bounds `loop_data_bounds_pre` needs, and `n <= tot`.
All three are computable from C2's recurrences plus the bases list. `P_mono` is
then generated with it.

**C4. Retire the redundant LoopSpec fields.** `loop_base`/`loop_base_pre`/`loop_base_post` and
`loop_counter_pre`/`loop_counter_post`/`loop_counter_post_ex` are one variable at three weakenings; the
In-proof trick (already demonstrated) collapses each triple to a name plus an
`∈` proof. This also makes `loop_runs`'s `Hpl`/`Hpa` STRUCTURALLY true instead
of `fun _ => eq_refl`.

**C5. The placement bundle.** `pia`/`pbound`/`Hq`/`Hok`/`HokF`/`Hwf` → one
record. `loop_runs` 20 args -> 15.

---

## Phase D — the obligation tactics

**D1. `solve_latch`** — dispatch on the guard family (`ptr` vs `ctr`) and on
the SIGN of `loop_counter_step` (`bv.of_N_add` vs `bv_of_N_wrap_dec`), discharging all
six/seven bullets. Both dispatches are decidable from the LoopSpec.

**D2. `solve_edge`** — the seven `loop_back_edge_std` bullets. Given C2, the counter
three are determined; the bounds bullet is already a fixed three-tactic script;
the walk bullet is determined; the cell trade is the affine set computation
(which cells overlap, which leave, which enter — the difference between D's
"replace both" and C's "slide by one" is READABLE FROM THE CELL SPECS: whether
the two offsets share a base variable).

**D3. `loop_enter_from_seg`** — the missing mirror of `loop_back_edge_std`: turn a
predecessor's `seg_exit_state` into `loop_invariant n`. Same cross-valuation machinery
(`gen_regs_at_inst`, `loop_reg_shift`, `loop_cell_shift`). Without it every
composition hand-rolls ~40 lines.

---

## Phase E — the one-lemma target

**E1. `loop_verified`** — takes the derived `LoopSpec`, the specification bits
(§0), and the two VCs; concludes `∀ n, Inv n -∗ myWP2_loop Post`. A companion
`solve_loop` discharges everything C and D generate.

**E2. `seg_chain`** — compose a list of segments and loops, framing an opaque
`iProp` throughout (the reservoir's channel, per B3).

Success criterion: a new counted loop is its instruction list, its publicness
marking, its footprint ownership, its exit postcondition — and two tactic
calls.

---

## Phase F — what is STILL automatable once A-E are done

A-E get to "instruction list + publicness + ownership + outermost posts + two
tactic calls". Several of those inputs are themselves partly derivable, and two
whole areas are untouched. Recorded here so the plan is honest about its own
ceiling rather than implying A-E is the end.

**F1. NESTED LOOPS — the structural omission.** `LoopSpec` is single-level
throughout and nothing in A-E changes that. An inner loop ought to become a
segment of the outer loop's body, which is what the segment machinery is for;
what is unexplored is the FRAME interaction — the outer invariant must be
framed across the inner loop, and the inner loop's own `Fr` has to thread
through it. No evidence either way on difficulty. Probably the next structural
piece after E.

**F2. INTERMEDIATE CUT ASSERTIONS.** §0 originally classified "the exit
postcondition" as irreducible specification. That is right for a chain's
ENDPOINTS and wrong in the middle: a cut assertion between two segments is
determined up to strengthening by the successor's precondition. In a composed
setting most cut assertions should be derived from their neighbours, leaving
only the outermost two free. Plausibly the largest single remaining win.

**F3. CELL SPECS ARE DERIVABLE.** Phase C derives the control-flow fields but
not the memory footprint. Given C2's `iota` plus a memory def-use pass over the
body, the addresses the loop touches per trip fall out — so `loop_extra_pre`'s cell
list is derivable. What stays human is whether the caller OWNS them (§0.2) and
their publicness (§0.1). Narrows the human input further than A-E does.

**F4. PUBLICNESS RELEVANCE.** A liveness analysis says which publicness
annotations cannot matter (dead after the loop), shrinking what a human must
decide without touching what publicness MEANS.

**F5. THE SOLVER RESIDUAL CATALOGUE.** `solve_symbase_fetch` is eight
alternatives accreted one per new program shape (the eighth landed
2026-09-13). That is an unbounded backlog by construction. The real fix is
teaching the solver about base-relative bounds rather than patching residuals
afterwards — work in `theories/Symbolic/Solver.v`, outside this plan's scope
but on its critical path eventually.

**F6. FUEL.** C1 says "step count plus slack", which is hand-waving. Too little
gives a misleading bare `False` (cfgver-solve-vc documents the trap); too much
inflates every VC. A bounded-step analysis would compute it.

**F7. FAILURE LOCALISATION.** Everything here fails as `No applicable tactic`.
For a system this automated the failure mode IS the user interface, and nothing
in A-E improves diagnosis. (This cost a detour through the `Ltac` body on
2026-09-13 when loop C failed; the warning now in `solve_param_vc`'s comment is
a note, not a fix.)

---

## Spike results (2026-09-13)

Both spikes from the execution order below have been RUN. Each changed the
plan: (a) made C2 much cheaper, (b) moved Phase B's cost into a different file
and a heavier chain.

### (a) Does IV analysis actually yield `iota`?  YES — 7/7, and it is a projection.

Checked against every loop in the tree expressed as a `LoopSpec`: A, B, C, D,
F, Tail (`Example/ZZLoopLatchCheck.v`) and divrem (`divrem_iota`, `Example/ZZDvLoopThm.v`).

Every component of every `iota` has the form `anchor + n · stride`, and **each
stride is already a literal field of the `LoopSpec`**:

| variable in `R` | stride (per unit of n, trips-REMAINING indexing) | where it already lives |
|---|---|---|
| the code base `"q"` | 0 | — |
| the counter (`loop_counter_pre`'s variable) | `−loop_counter_step` | `loop_counter_step` |
| each walking pointer | `−walk_step` | `walk_reg` in `loop_extra_pre` |
| anything else | 0 (must be, or the loop is out of scope) | — |

So deriving `iota` needs no pass over the instruction list. C1 already has to
find the strides to build the `LoopSpec` at all; C2 then just reads them back.

**The counter's anchor is FORCED, not chosen.** Writing `counter(n) =
sentinel − (n+1)·imm` with the sentinel read off `loop_exit_guard` reproduces all
seven hand-written values exactly — δ = 1 uniformly, across both relop families
(`eq`/`neq` and `bvule`/`bvult`), both stride signs (±1, ±4), and both literal
(A, B, dv) and variable (C, D, F, Tail) sentinels. It is forced because it is
precisely what `loop_latch_obligation` demands, and `loop_latch_obligation` is two-sided —
the exit must hold at trip 0 AND the guard at every trip above it. For the
equality family the exit alone pins it; for the inequality family (A, dv) it
genuinely takes both: with `counter(n) = a + n`, `exitg` gives `a ≤ 2` and
`guard` gives `a ≥ 2`. Checked numerically over n ∈ [0,40) including
uniqueness against every anchor shifted by ±1..8 strides: unique in all seven.

**What is NOT derived:** one anchor per non-counter walking pointer (`p7e`,
`p6e`, `ape`, `spb`). These are free parameters of the loop's contract, which
is correct — they are what the predecessor segment supplies.

**Honest limit on the evidence.** This samples loops that were *already*
expressed as `LoopSpec`s, i.e. the successes. It confirms the abstraction is
faithful to every loop currently in it (which was not obvious — `ls_at`, see
below, suggested drift). It says nothing about a loop that has never been
attempted, and the §0 scope limit on non-affine IVs stands unchanged.

**Incidental finding — `ls_at` is vestigial and inconsistent.** For the
countdown loops (A, B, dv) `ls_at` IS the counter's `iota` component
(`n+2`, `n+1`, `n+2`); for the pointer loops (C, D, F, Tail) it is `fun n => n`,
which is not the counter's value or anything else. `ZZLoopCProbe.v`'s own
comment says it "is not consulted by the contracts at all". Fold its removal
into C4 (retire the redundant `LoopSpec` fields) — but note that in three of
seven loops it happens to hold the right thing, so deleting it is not free of
meaning: C2 should SUPERSEDE it rather than drop it.

### (b) Does a base-relative `mem_full_spec` break an end theorem?  NO — but that was the wrong question.

Probe: `Example/ZZSpikeMemBase.v` (untracked). It defines a genuinely different
memory-spec vocabulary — `mem_spec_at : N * N * bool * param_val`, where each
entry NAMES ITS OWN BASE rather than sharing the implicit code base — restates
cmovznz4's end theorem over it, and re-derives it from
`cmovznz4_noninterferent_param`. Compiles; `Print Assumptions` on the restated
theorem gives exactly `pure_decode` and `mmioenv`, the two whitelisted axioms.
So the trusted statement surface tolerates the new form with no loss.

Three findings, in increasing order of how much they change the plan:

1. **Base-relative data already exists and is in production.** `mem_spec_rel`
   (`N * bool * param_val`, address `p + k`) plus `concretize_mem` is how
   cmovznz4 is stated. Phase B's opening premise was simply false; corrected in
   place above.

2. **The single-base assumption is cheap to lift.** 25 sites, all in
   `GenContract.v` (22), `EndToEnd.v` (2), `GenCompose.v` (1). The soundness
   chain — `Verifier`, `VerifierRel`, `Adequacy`, `Spec`, `SpecIris`, `Tables`,
   `TablesRel` — has ZERO. It is already generic in Σ.

3. **The actual blocker is `HDataAddrs`, and it is not about addressing at
   all.** Every EndToEnd bridge carries
   ```
   ∀ i spec, data_specs !! i = Some spec →
     spec.1 = bv.of_N (init_addr + 4*|instrs| + 4*i)
   ```
   — the data words must occupy the 4·|data| bytes IMMEDIATELY AFTER the code,
   contiguously. The probe proves the consequence: handing the bridge cmovznz4's
   specs at any other base `arr` forces `bv.of_N (arr+116) = bv.of_N (ia+116)`,
   i.e. it pins the data base to the code base
   (`data_base_pinned_by_HDataAddrs`).

   It is consumed by `Adequacy.v`'s `instrsAndDataMemory`, which splits
   `liveAddrs` four ways (`before ++ instrs ++ data ++ rest`) to carve the data
   region out of raw byte ownership, then inducts along one contiguous run.
   Supporting an independent data base means generalising that to k disjoint
   runs with ordering/disjointness hypotheses — **work in the HEAVY chain, not
   in `GenContract.v`.**

   Consequence worth stating plainly: **no example in this tree has ever had
   data at a base independent of its code.** Every example with memory puts its
   array immediately after the instructions. A loop over a caller-supplied
   array — the thing Phase B exists to make expressible — is therefore blocked
   on an `Adequacy.v` change that nothing has needed so far.

---

## Step 1 results (2026-09-13) — A3 + C4 + C5 landed

All three done, plus two derivations that fell out of A3. Every loop VC and
every composition probe re-verified; `GenCompose.vo` is already a gate build
target, so this is gate-covered.

**A3 — `gen_loop_contract` now delegates to `gen_seg_contract`.** A loop's
contract IS an ordinary segment contract, entered at head 0 of its own code
base. The risk was never the statement, it was the *precondition order*:
`gen_seg_contract` puts the code bound second and the register block last,
where the loop generator buried both mid-frame, and conjunct order moves
consume-scan positions. Measured before committing to it
(`Example/ZZSpikeA3.v`, loop D — two walking pointers, two cells, three base
bounds): both contracts verify with a bare `solve_param_vc`. All 14 loop VCs
(7 loops x body+final) then re-verified with **no tactic changes at all**.

Consequences in the generated contract, none cosmetic: `cfg_placement` is
`loop_base + 0` and `cfg_init_addr` is `loop_head_addr + 0`, neither definitionally the bare
form (`N.sub`/`bv.add` do not see through a variable), so the composition
lemmas pick up an `inst_addr_plus0`. `cfg_exitCond` is unchanged. Four
projection lemmas (`gen_loop_place`/`_exitCond`/`_instrs`/`_exits`) keep the
composition layer from ever cbn-ing through `gen_seg_contract`'s
`let place := …`; three are `eq_refl`, and only `gen_loop_exits` needs work,
because `t - 0` is STUCK for a variable `t`.

**A3, second half — `loop_body_trip` and `loop_final_trip` are now ONE lemma.**
`loop_one_trip`, parameterised by the guard, the target, the valuation and the
continuation; the two are three-line corollaries. They had been ~40 lines each
differing only in those four things, with both faith arguments and the entire
HPre bullet duplicated verbatim.

**Derived: `loop_code_extent` (= `4 * loop_num_instrs`) and the code base's bounds entry.** The
code extent used to be hand-written as the LEADING entry of `loop_data_bounds_pre` /
`loop_data_bounds_post`, where it had to agree with `loop_num_instrs` and (for a bottom-tested
loop) with `loop_exit_off`, and nothing checked it. 7/7 loops had all three equal.
`ls_bases_*` now carry DATA bases only and `loop_all_bounds_pre/_an` prepend the
derived entry — which is also what keeps the frames symmetric, so
`loop_frame_transfer`, `loop_back_edge`, `loop_back_edge_std` and `loop_runs` needed no
restructuring at all. (The first attempt made the frames asymmetric and would
have rewritten all four; reverted before compiling.)

**C4 — six LoopSpec fields become two.** `loop_base`/`loop_base_pre`/`loop_base_post` and
`loop_counter_pre`/`loop_counter_post`/`loop_counter_post_ex` were one variable at three weakenings each;
they are now `loop_base_var`/`loop_base_in` and `loop_counter_var`/`loop_counter_in` (a name plus its
membership proof, written `_` in a literal and resolved by `ctx.resolution`),
with the six Terms derived. Validated in 56 ms before any editing: `_` does
resolve under record syntax, and `loop_base ls` is DEFINITIONALLY the `term_var "q"`
the literals used to spell out — so C4 changed no contract and re-proved no VC.
It also kills `loop_runs`'s `Hpa` premise, since `inst (loop_base_pre ls) (i.["a"↦w])
= inst (loop_base ls) i` is now `reflexivity` (`inst_loop_base_pre`).

**C4, continued — `ls_at` deleted.** Spike (a) found it vestigial and
inconsistent (the counter's `iota` in the three countdown loops, `fun n => n`
in the four pointer loops) and nothing referenced it outside its own
declaration. The information is not lost: spike (a)'s closed form derives it.

**C5 — the placement bundle.** `pia`/`pbound`/`Hq`/`Hok`/`HokF`/`Hwf` become
one `LoopPlace` record; `loop_instr_block ls pl` replaces the `ptsto_instrs (… <$>
instrs_of_list (of_N pia) …)` block every statement re-spelled. `loop_runs` goes
from **22 arguments to 16**.

**Two traps worth keeping.**

1. **Do NOT make the C4 accessors `Arguments … : simpl never`.** It looks right
   — it restores the stuck-on-a-variable behaviour of the record projections
   they replace — and it fixes this file's own latch lemmas. But it is too
   blunt: every example proof relies on `cbn` reducing `loop_counter_pre (mulinner_spec iq)`, a
   projection of a CONCRETE record, down to `term_var "p1"`, and blocking the
   definition blocks that too. The problem is only the VARIABLE case, in six
   sites inside `GenSegment.v` and `GenCompose.v`, which say
   `cbn -[loop_counter_pre]` / `cbn -[loop_base_pre]` / `cbn -[loop_counter_post_ex]` instead.
2. **`loop_code_extent` is not cbn-reducible in the bounds bullet.** `cbn` will not
   delta-expand it (its body starts with a multiplication, not a match), so the
   standard `loop_bound_le` incantation needs `try unfold loop_code_extent` for the
   code base. The `try` is because the data bases are still literals; if it ever
   fails to fire where it should, the following `lia` fails loudly.

---

## Step 2 results (2026-09-13) — D3 `loop_enter_from_seg`

**Delivered (GenCompose.v):** `loop_entry_obligation` (the assertion-level obligation, as
a named Prop mirroring `loop_back_edge`), `loop_enter_from_seg` (turns a predecessor's
`seg_exit_state` into `loop_invariant n`), and `seg_then_loop` (`seg_then` with the cut
filled in — run the predecessor, land in the loop, run the loop). All three
compiled first try.

**The premise that justified promoting this was right.** Nothing in the tree
had ever ENTERED a loop: `seg_exit_state` appeared only as a loop's *output*, in
`loop_final_trip`. So the entry side really was analysis-only.

**The analysis HELD.** Exercised on the one real loop-entry site in the tree —
`sgL` (muladd instrs 250..263, head 1000) falls through at offset 1056, which
is exactly the tail loop's head (`loop_first_instr` 264). Probe:
`Example/ZZSpikeEnter.v` / `ZZSpikeEnterA.v` (untracked).

- The two sides are in DIFFERENT contexts (`["p"]` vs
  `subword_ctx = ["q";"ap";"bp";"e"]`), as predicted — and `loop_reg_shift` /
  `loop_cell_shift` are ALREADY `{R1 R2 : LCtx}`, so the back edge's
  cross-valuation machinery transfers to the entry direction unchanged. That
  was the main thing in doubt.
- The entry arithmetic is FORCED, not chosen: `subword_iota`'s `bp(n) = pe - 4(n+1)`
  plus sgL handing over A4 = p+1144 and A2 = p+1152 pins `pe = ia+1152` and
  `n = 1`; A0 = p+1132 then pins `ape = ia+1140`; and `tot = 1` because
  `loop_completed`'s window must be empty at entry. All of that agrees with
  `sgL_post`'s own comment ("exactly two trips").
- `loop_reservoir` at trip 0 is EXACTLY sgL's declared second window (p+1136 /
  p+1148). The reservoir lines up with no adjustment.
- The resources the loop never touches (four spill slots, X2/S0-S3, the
  program bound) frame with a bare `iFrame`.

**Then finished, by changing the layer.** The hand reconciliation was
abandoned; `Example/ZZSpikeEnter{,A}.v` have been deleted. The replacement,
`Example/ZZSpikeEnter2.v`, compiles in **25 s** with no `admit`, and proves the
same thing the hand version could not.

**What was wrong was the LAYER, not the tactics.** `sgL_post` and
`gen_loop_at_head (subword_spec …)` describe the same machine state in two spellings, and
I was reconciling them resource by resource inside Iris. Two separate blowups
made that visible before the diagnosis did:

- a blanket `cbn` on an `inst` goal took the file from 30 s past 4 minutes,
  TWICE — it unfolds `bv.of_N` at width `xlenbits` (the `bv-pitfalls` trap in a
  new place; use `inst_addr_plus` + `bv.of_N_add`);
- and even with every address fact hoisted and `cbn`-free, `iApply
  (loop_cell_shift …)` INSIDE the entry proof did not finish in 4.5 minutes,
  while the identical applications in a separate file were part of a 21 s
  compile. Elaborating implicit arguments against a context holding the whole
  unfolded `sgL_post` is what costs.

**The fix is F2, made concrete: GENERATE the cut assertion from the successor's
precondition.** A predecessor's post is stated as `subst (gen_loop_at_head ls) ζ ∗
Rest`, and the entry obligation stops being a separation-logic proof and
becomes a VALUATION EQUALITY. Three pieces:

1. **`asn.interpret_subst`** (`theories/Syntax/Assertions.v`) — substitute then
   interpret = interpret under the substituted valuation. Did not exist; ~20
   lines by induction, needing a new `interpret_chunk_subst` in `Chunks.v`.
2. **`loop_entry_by_subst`** (GenCompose) — six lines of proof. `ζ` does BOTH jobs
   at once: it carries the predecessor's context `S` to the loop's `R` (sgL is
   at `["p"]`, the tail loop at `["q";"ap";"bp";"e"]`) AND absorbs the extra
   `"an"` binder, so no separately shifted copy of `gen_loop_at_head` is needed.
3. **`Rest` is not optional.** A predecessor's post must return everything its
   PREcondition consumed or the executor drops it — sgL owns ten data cells and
   hands the loop two. So the cut is `successor's precondition ∗ frame`, and
   the frame is exactly what the loop rides over (here: the second window,
   which becomes the loop's reservoir, plus the spill slots and X2/S0-S3).

**And sgL still verifies.** `valid_sgL'` — sgL's contract with its hand-written
`sgL_post` replaced by the generated one — is a bare `solve_param_vc`. That was
the real risk and it did not materialise.

**A FRAMEWORK BUG, found on the way.** `sub_assertion` mapped `or` to **`sep`**
(`Assertions.v:125`), while `interpret` maps it to `∨` — so substituting an
assertion containing a disjunction changed what it meant. `asn.or` is live
(both the symbolic and shallow executors consume it). `interpret_subst` is
exactly the statement that was false because of it, which is how it surfaced.
Fixed.

**AND THE COMPOSITION IS DONE.** `sgL_then_tail` (`Example/ZZSpikeEnter2.v`)
composes sgL with the tail loop end to end: axiom-clean, no `admit`, whole file
27 s. It is the first time anything in this tree has ENTERED a loop. Four
things had to be added on the way, and three of them are reusable:

- **`seg_run_pinned_exit`** (GenCompose) — sgL declares TWO exits (the
  fall-through into the loop and a branch that skips it when the trip count is
  zero), so `seg_run_single_exit`, which pins the exit from the exit CONDITION, does not
  apply. When the postcondition says which exit was taken, the segment can
  still be composed as single-exit, and the VC then has to prove the others
  unreachable — which is where that obligation belongs. Adding `an = p+1056`
  to sgL's post left `solve_param_vc` unchanged, so the skip really is dead.
- **`loop_back_edge_frame`** (GenCompose) — an edge proved for one frame holds for
  that frame plus a constant carry, which is how a predecessor's leftovers
  (spill slots, callee-saved block) thread through a loop whose edge lemma was
  stated for the reservoir alone.
- **The RESERVOIR is also a substitution.** `loop_reservoir` is an iProp built from a
  `[∗ list]` and so cannot BE a postcondition (B3) — but at a CONCRETE entry
  trip count it is finitely many copies of the loop's own cell assertion, each
  that assertion substituted at that trip's valuation. So the same mechanism
  covers it; `sgL_rest` carries `subst (gen_cells_pre subword_cells) subword_reservoir_subst`.
- **`subword_exit_post` / `valid_lt_final`** — `ZZLoopTailProbe` only ever stated the loop
  BODY's contract. `loop_runs` needs both.

**A SECOND BUG, and a worse one than the `or` slip.** `LoopPlace`'s `place_body_table_ok` /
`place_exit_table_ok` stated their target lists HEAD-RELATIVE (`[0%N]`, `[loop_exit_off ls]`) —
the convention a loop's EXIT table uses. But `seg_placement_ok`'s last conjunct is
`forallb (fun t => head <=? t) targets` with `head = 4*skip`, so `1056 <=? 0`
made the field **unsatisfiable for every loop at a nonzero offset**. Every loop
theorem taking it as a hypothesis — `ZZLoopDThm.mulinner_loop_runs`,
`ZZDvLoopThm.divrem_loop_runs` — was therefore VACUOUS, and nobody noticed because the
premise was always assumed and never discharged. It surfaced only here, where
`subword_place` had to actually *prove* it and `vm_compute` answered `false`.
`seg_instr_table_ok`, the only consumer, uses just `seg_placement_ok`'s offset/skip/size
parts and ignores the targets, so the fix is to state them program-relative
(`4*skip + target`). No tracked end theorem was affected — none goes through
`loop_runs` — so nothing false was ever claimed on the trusted surface.

---

## Step 3 results (2026-09-14) — C1 landed (narrow form)

**What it is.** `GenSegment.v` gained `LoopShape` + `loop_shape_at`, which
derives six of a LoopSpec's fields from the instruction list plus ONE input:
the back edge's list index. The wide form (scan for a branch whose target is
at most its own address) was considered and rejected — the caller always knows
which loop they mean, so naming its back edge costs one number and buys the
rest.

**Fields derived:** `loop_first_instr`, `loop_num_instrs`, `loop_exit_off`,
`loop_fuel` (= body length + a caller-supplied slack), `loop_guard`,
`loop_exit_guard`.

**NOTHING C1 PRODUCES IS TRUSTED, and that is what buys the API.** Every field
is re-checked downstream — the instruction table by `seg_placement_ok`, the
extent and both guards by the VC itself. A wrong derivation cannot make a false
theorem, only fail to prove a true one. So `loop_shape` is TOTAL (empty body as
the junk value) rather than threading an `option` through every LoopSpec
literal, with `loop_shape_found` as the `vm_compute`-checkable early error.

**The guards are a TABLE, not a relop flip.** The LoopSpec record's own comment
warns that "flipping a relop mechanically would be wrong for some comparison",
and that warning stands — `shape_guards` is six explicit rows (one per `BOP`),
each naming its exact complement, doubled for whether the counter is the
branch's first or second operand. It is available for all six only because
RISC-V's branch conditions are equality plus two total orders, so `not (a <u b)`
really is `b <=u a` at the same signedness. A generic `formula_not` would have
been the unsound shortcut. Operand ORDER is preserved rather than normalised,
because the solver matches terms syntactically.

**Proved, not assumed:** `loop_shape_at_spec` — a `Some` really does mean the
branch at `back` targets the head (which is what licenses
`loop_body_contract`'s exit target `0%N`) and the body really is head..back
inclusive (which is what makes `shape_exit_off` the fall-through).

**Exercised on the two loops that differ, and it reproduces both EXACTLY,
operand order included:**

| loop | back edge | counter side | derived guard / exit guard |
|---|---|---|---|
| `mulinner` (D) | `bne A1, T1, -112` @ idx 218 | rs1 | `neq c e` / `eq c e` |
| `countdown` (A) | `bltu A5, A4, -96` @ idx 40 | **rs2** | `bvult other c` / `bvule c other` |

`countdown` is the load-bearing one: its counter is the branch's SECOND
operand, so it exercises the mirrored half of the table, and its "other"
operand is a `term_val` (a register holding the constant 1) rather than a
variable. Both `_spec`s now take all six fields from their shape and carry a
`_shape_values` regression lemma pinning the derived numbers to the
hand-written ones.

**The risk that did not materialise.** The latch lemmas take
`Hg : loop_guard ls = fun t => ...` as a HYPOTHESIS, discharged by callers with
`eq_refl`. A derived guard still closes these by conversion —
`ZZLoopLatchCheck`, both `ZZLoopTransCheck`s, `ZZLoopDThm`, `ZZSpikeA3` and
`ZZSpikeEnter2` (the assembled `sgL_then_tail`) all rebuild green with no
change.

**Two method notes.** (1) The lemma statement AND one interior `assert` both
had to be respelled with `@eq`/`Z.mul` — infix `=`/`*` in `GenSegment.v`
elaborate against `Term _ ty.int` (rocq-pitfalls' notation hijack; `Contracts.v`
already uses the `@eq Z` idiom for the same reason). (2) `lia` does not connect
`Z.rem _ 4 = 0` to divisibility on its own; that needs an explicit
`Z.rem_divide` step.

**NOT done, deliberately.** `loop_counter_step` is still hand-written. It is a
one-instruction body scan (`addi ctr, ctr, imm` with `rd = rs1 = ctr`) and
would remove the last field that must silently agree with the code, but it is
C2's input, not C1's output — see C2.

---

## Step 3 results, part 2 (2026-09-14) — C2 landed, at the LATCH level

**Scope changed from what the plan said, deliberately and with the user's
call.** The plan scopes C2 as "derive `iota`". Measuring the duplication first
said `iota` is the smaller half: the six `*_iota` + `*_latch` pairs are 146
lines, of which the `iota` definitions are ~30; `mulinner_latch` and
`walkup_latch` are byte-identical apart from variable names. Deriving `iota`
alone would have left every `refine (loop_latch_ptr ...)` and its seven bullets
standing. So C2 derives the LATCH OBLIGATION, with `iota` still supplied by the
caller and only *checked* against the affine closed form.

**The forced `+1` is the thing actually removed.** Spike (a) found the counter's
anchor is not chosen but forced — `counter n = sentinel − (n+1)·imm` is exactly
what `loop_latch_obligation` demands, because it is two-sided (exit at trip 0,
guard above it). That `+1` is invisible in the goal and fails late. It now lives
in `loop_ctr_down` / `loop_ctr_up` and nowhere else.

**Delivered:** `loop_ctr_down`, `loop_ctr_up`, and three wrappers —
`loop_latch_ptr_affine_down`, `loop_latch_ptr_affine_up`,
`loop_latch_ctr_affine_up`.

**TWO AXES, NOT ONE — a correction to this plan's own framing.** I assumed the
`ptr` family counts down and the `ctr` family up. That is wrong. The GUARD
FAMILY (`ptr` = neq/eq against a term, `ctr` = bvult/bvule against a literal)
and the DIRECTION are INDEPENDENT:

| loop | guard family | direction | anchor, stride |
|---|---|---|---|
| countdown (A) | ctr | up | 1, 1 |
| divrem | ctr | up | 1, 1 |
| shiftdown_ctr (B) | **ptr** (vs literal 0) | **up** | 0, 1 |
| shiftdown_ptr (C) | ptr | **up** | pe, 4 |
| mulinner (D) | ptr | down | pe, 4 |
| walkup (F) | ptr | down | pe, 4 |
| subword (Tail) | ptr | down | pe, 4 |

So `ptr` needs both directions. `ctr` has only `_up` because no loop in the tree
counts the other way — an absence, not an impossibility; say so rather than
implying the case cannot arise.

**`anch` is ONE number, not two.** In the pointer family the counter's anchor
and the limit's value are the same — that is the forced-anchor finding restated,
since the loop stops exactly when the counter reaches the limit. Taking them as
separate parameters would have let a non-terminating loop typecheck.

**Payoff, measured.** The six latch proofs in `ZZLoopLatchCheck.v`: 96 → 55
lines of `Proof..Qed`, and the per-loop data drops from three hand-written
closed forms (`kv`, `w`, `ev`) to an anchor and a stride. `Hk`/`He` stay
`cbn. reflexivity.` on the loops that had them — the arithmetic regression I
feared at the `iota`-only level does not occur here, because the user never
writes `Hk` for the parts that differ.

**One asymmetry that is real, not an oversight.** `_ctr_affine_up` and
`_ptr_affine_up` need `stride < bv.exp2 xlenbits`, `_down` does not: the up
direction encodes its step as the wrap-around `2^32 - stride`, which only
denotes a decrement while the stride fits in a word. `_up` in exchange needs no
separate `Hb`, since its `HPb` at trip 0 already bounds the anchor.

### A METHOD CORRECTION that invalidates an earlier green — read this

`rocq_compile_file` on a `CFGVer/Example/ZZ*.v` file compiled it against a
**stale `GenSegment.vo` in `_build/default`**, not the source tree. So the
"whole chain rebuilds green" reported for C1 was not a real check: rebuilding
the same files with plain `coqc` and the `_CoqProject` flags found TWO genuine
failures that `rocq_compile_file` had reported green —

1. `@eq N (shape_exit_off _) 116` — `116` parsed as `nat`. Needs `116%N`.
2. `ZZLoopTransCheck.v:202`'s `lia` — `loop_num_instrs` now routes through
   `shape_num_instrs`, and `cbn` cannot reduce `loop_shape_at` (it would have to
   unfold `nth_error` over a 282-element list and `bv.signed` under it), so the
   code-extent bound became an opaque atom.

Fix for (2), and it is the general rule for any C1 consumer: define the shape
with **`Eval vm_compute in`**, so the record is a LITERAL at definition time and
every downstream `cbn` behaves exactly as it did when the fields were typed by
hand. This costs nothing in checking power — a bogus shape still makes
`_shape_found` and `_shape_values` fail.

**Rule going forward: these probes are verified with `coqc` + the `_CoqProject`
flags, not with `rocq_compile_file`.** The ZZ files are not in `_CoqProject`, so
`make` does not know them either; the invocation is
`coqc -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran <flags> <file>.v`
run from the repo root.

---

## Step 3 results, part 3 (2026-09-14) — C3 landed

**Delivered:** `trip_axis` (`TripDown`/`TripUp`), `trip_axis_bound`,
`trip_tail`, `loop_trip_bound`, `loop_trip_bound_mono`, and the two
`+2`-to-`+1` projections `trip_axis_down_latch` / `trip_axis_up_latch`.

**The `+2` is the point.** The latch reads trip `n`, so it wants the bound at
`n+1`; the BACK EDGE reads trip `S n`, so `P` must cover one trip more. That
off-by-one between two consumers is invisible in a goal and fails late. It now
lives in `trip_axis_bound` once, and the weakening to what the latch wants is a
named lemma rather than an anonymous `lia`.

**The trip cap is an `option`, deliberately.** `P` is a HYPOTHESIS the caller
establishes, so every clause added to it makes the loop's theorem WEAKER.
divrem genuinely has no trip cap; giving it one to make the shape uniform would
have silently strengthened its premise. `None` costs a trailing `/\ True`,
which is cheaper than that.

**A design constraint worth recording: EVERYTHING MUST REDUCE UNDER ONE `cbn`.**
The first draft made the cap a `nat -> Prop` parameter with `trip_within` /
`trip_unbounded` as its two instances. That typechecks and `_mono` goes through,
but `cbn` will NOT unfold `trip_within` — its body is a lambda, not a match — so
every call site needed an extra `unfold` on top of the `cbn`. Counting lines,
that made C3 a NET LOSS: the three predicates plus three `_mono`s saved ~12
lines, and the added tactic noise cost more. Rewriting the cap as
`trip_tail : option nat -> nat -> Prop`, a match, fixed it: one
`cbn [loop_trip_bound List.fold_right trip_axis_bound trip_tail]` is the whole
incantation, and `loop_trip_bound_mono` lost its side premise about the cap.

**Wired:** `mulinner_trip_bound` = `[TripDown pe 4; TripDown p7e 4] (Some tot)`,
`subword_trip_bound` = `[TripDown pe 4; TripDown ape 4] (Some tot)`,
`divrem_trip_bound` = `[TripUp 1 1] None`. Each `_mono` is now
`exact (loop_trip_bound_mono _ _ n).` All 17 probe files rebuild green with
the real compiler.

**Honest accounting.** C3 is roughly line-neutral, unlike C1 and C2 which won
on lines as well. What it buys is that the axis shape and the `+2` are DATA
rather than hand-typed arithmetic — which is what a generator needs, and what
makes `P` derivable from C1's strides once C1 also derives `loop_counter_step`.

---

## Execution order

NOT A-E in sequence. Two principles override the grouping: resolve the
unknowns before investing in what depends on them, and unblock a real task
early — today a loop cannot be composed with a neighbour at all.

**0. Two spikes. DONE 2026-09-13 — see §Spike results.** Both landed; the
order below is the REVISED one, and the revision is the point. Spike (a) made C
cheap, so C moves ahead of B. Spike (b) moved B's cost out of `GenContract.v`
and into `Adequacy.v`, so B drops to last and acquires a go/no-go.

**1. A3 + C4 + C5 — the loop layer's own cleanup. DONE 2026-09-13.** See
§Step 1 results below.

**2. D3 (`loop_enter_from_seg`). DONE 2026-09-13** — see §Step 2 results below.

**3. C1, C2, C3 — PROMOTED past A1/A2 and past B.** Two reasons from spike (a):
C2 is a projection off fields C1 must compute anyway, so C1→C2 is nearly free
once C1 exists; and C no longer waits on B, because the convergence direction
is mem-spec → `cell_spec`, i.e. the loop-side cell vocabulary is the STABLE
side. The old ordering had C behind B on the guess that B1 might rewrite
`cell_spec`; spike (b) says B1 rewrites `mem_spec_rel` instead.

**4. D1, D2.** Follow C directly — both are driven by C2's output, and D2's
cell-trade dispatch (which cells leave, which enter) is the affine set
computation over `iota`. No longer gated on B, same reason as step 3.

**5. A1 + A2, batched.** Pure hygiene, both touch the contract record, both
need a full gate. One gate run, not two.

**6. E.**

**7. B — memory addressing, LAST, and behind a go/no-go.** Spike (b) turned
this from "the phase that changes the trusted statement surface" into "the
phase that changes `Adequacy.v`". Decide B1' (k disjoint data runs) explicitly
before touching B1 — B1 alone buys nothing, and B1' is the only thing standing
between this machinery and a loop over a caller-supplied array. If the answer
is no, say so in §0 as a scope limit rather than leaving B half-built.

Then F, in whatever order the work at the time demands; F1 and F2 are the two
worth doing.

**Risk notes.** REVISED. B remains the phase to be careful with, but not for
the reason previously given: the trusted STATEMENT surface tolerates a
base-relative form (spike (b), proved), while `Adequacy.v`'s contiguity
assumption does not generalise for free. C2 is no longer the largest single
piece of real work — B1' is. Every phase touching `Contracts.v`,
`mem_full_spec` or the generators needs a full rebuild and the gate behind it
(~45 min on this box at GATE_JOBS=1).
