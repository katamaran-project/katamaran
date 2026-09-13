# PLAN — loop automation: get the specification right, apply one lemma

Target: once the SPECIFICATION is written, obtaining a loop's contract and
composing it with its neighbours is an application of a lemma plus a tactic,
with no hand-written glue.

Written 2026-09-13, after `loop_all` / `loop_edge_std` / `loop_latch_obl` /
`loop_done` landed (commits 0568430f, e6cd34fc, 554f7cc7) and the composition
interface was read off an unfolded `ldInv`.

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
(`loop_res`'s `[∗ list] i ∈ seq 0 n` becomes a recursive list-segment
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
soundness bridge currently has to PROVE they agree (`seg_exits_faith`,
`etable_rel`). Deriving makes that obligation vanish by construction.

**A2. `extend_to_minimal_post`.** `CFG_VC_triple` wraps the PRE in
`extend_to_minimal_pre`; the POST is wrapped by hand in each generator as
`(post ∗ minimal_pre)`. GenSegment's own comment records the failure mode when
a generator forgets: the post consumes `cur_privilege`/`inv_leakage`, so the
body runs exactly once, failing late and confusingly. Make it structural.
*Measure*: this puts `minimal_pre` into every VC uniformly, paid at
`vm_compute` scale on ~30 examples. Expected nil, not free.

**A3. `loop_final` should BE an ordinary segment.** It composes today
(`loop_exit` is `seg_step1` underneath) but cannot be STATED in ordinary-segment
vocabulary, because `gen_loop_contract` forces the pre to `gen_loop_core ∗
guard`. Restate:
```
loop_final ls post := gen_seg_contract ... (extra_pre := gen_loop_core ls ∗ exit-guard) post
```
Then `loop_exit` collapses into `seg_step1`, and `loop_step`/`loop_exit` become
one lemma parameterised by the guard and the target.

**A4. Try moving `gen_pures` into `extra_an`.** Every edge proof has an `Hf`
bullet re-proving facts (`p1 ≠ p7`, range facts) that the post drops. They are
CONSEQUENCES of the previous trip plus the walk, not free choices, so the
executor could discharge them at the end of the body and `Hf` would disappear.
*Risk*: moves a one-line `lia` into the VC. Measure before adopting.

---

## Phase B — give DATA the base/offset treatment CODE already has

This is the structural gap, and it is why the reservoir has no origin.

Code is addressed base-relatively (`cfg_placement` + offsets). Data is not:
```
(* mem_full_spec: (address, is_public, optional_init_value) *)
gen_mem_asn: ... term_val ty_xlenbits a ↦ₘ ...     (* a CONCRETE literal *)
```
while the loop layer invented `cell_spec` with `cs_var` (base VARIABLE) +
`cs_off`. Two incompatible addressing schemes for data, so the whole-program
precondition and a loop's `loop_res` cannot be the same statement.

**B1.** Give `mem_full_spec` a base-relative form, sharing `cell_spec`'s
vocabulary. One addressing scheme for data.

**B2.** The bridging lemma: whole-program memory precondition ⊢ `loop_res` /
`loop_done` blocks. `loop_res_words` and `mem_word` are the loop-side half and
already exist; B1 supplies the other half. This is what makes an array
expressible end to end.

**B3.** Consequence to check, not assume: a `CFGVerifierContract`'s post is an
`Assertion Σ` over a FIXED `Σ`, so it can never mention `n` cells. The reservoir
must therefore still be threaded as `seg_step1`'s opaque `iProp` frame. B1/B2
make the ENDPOINTS expressible; they do not remove that constraint.

---

## Phase C — derive the mechanical LoopSpec fields

**C1. Placement and control flow** — `ls_skip`, `ls_take`, `ls_exit`,
`ls_guard`, `ls_exitg`, `ls_fuel`. All computable from the instruction list: a
CFG pass finds the back edge and the fall-through, decode gives the branch
relop, fuel is the step count plus slack. Deliver as a Gallina function
returning a `LoopSpec` skeleton, with well-formedness `vm_compute`-checkable.

**C2. `iota` from induction-variable analysis.** THE big one: five lines per
loop, but `Hk`, `Hkn`, `Hw`, most of `P`, and the affine part of the cell trade
all hang off it. For affine IVs with constant stride this is the standard
analysis and is decidable. Output: `iota` plus the per-variable recurrence,
with the correctness side condition discharged by `lia`.

**C3. Derive the trip predicate `P`.** It must imply exactly: the no-wrap
bounds the latch needs, the address bounds `ls_bases_a` needs, and `n <= tot`.
All three are computable from C2's recurrences plus the bases list. `P_mono` is
then generated with it.

**C4. Retire the redundant LoopSpec fields.** `ls_q`/`ls_q_a`/`ls_q_an` and
`ls_k_a`/`ls_k_an`/`ls_k_anc` are one variable at three weakenings; the
In-proof trick (already demonstrated) collapses each triple to a name plus an
`∈` proof. This also makes `loop_all`'s `Hpl`/`Hpa` STRUCTURALLY true instead
of `fun _ => eq_refl`.

**C5. The placement bundle.** `pia`/`pbound`/`Hq`/`Hok`/`HokF`/`Hwf` → one
record. `loop_all` 20 args -> 15.

---

## Phase D — the obligation tactics

**D1. `solve_latch`** — dispatch on the guard family (`ptr` vs `ctr`) and on
the SIGN of `ls_imm` (`bv.of_N_add` vs `bv_of_N_wrap_dec`), discharging all
six/seven bullets. Both dispatches are decidable from the LoopSpec.

**D2. `solve_edge`** — the seven `loop_edge_std` bullets. Given C2, the counter
three are determined; the bounds bullet is already a fixed three-tactic script;
the walk bullet is determined; the cell trade is the affine set computation
(which cells overlap, which leave, which enter — the difference between D's
"replace both" and C's "slide by one" is READABLE FROM THE CELL SPECS: whether
the two offsets share a base variable).

**D3. `loop_enter`** — the missing mirror of `loop_edge_std`: turn a
predecessor's `seg_exit_at` into `loop_inv n`. Same cross-valuation machinery
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
body, the addresses the loop touches per trip fall out — so `ls_extra_a`'s cell
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

## Execution order

NOT A-E in sequence. Two principles override the grouping: resolve the
unknowns before investing in what depends on them, and unblock a real task
early — today a loop cannot be composed with a neighbour at all.

**0. Two spikes first.**
   - Does IV analysis actually yield `iota` for the five existing loops?  Not
     the implementation, just enough to know.  If it does not, C2 collapses and
     with it D1, D2, and most of §0's "derivable" classification.  Everything
     downstream is priced on this being routine.
   - Does a base-relative `mem_full_spec` break an existing end theorem?  Write
     the new form alongside the old on ONE example and re-run that theorem.
     `mem_full_spec` is the trusted statement surface; discovering a problem
     after B2 is built on top is the worst case.

**1. A3 + C4 + C5 — the loop layer's own cleanup.** Self-contained, no
trusted-surface impact. A3 matters most: collapsing `loop_final` into an
ordinary segment turns `loop_step`/`loop_exit` into one lemma, and that lemma
is what D and E build on. Doing it after E means rebuilding E.

**2. D3 (`loop_enter`) — PROMOTED from near-last.** It is what makes
composition possible at all; it is independent of C2 (it can take `Fr n` as an
opaque hypothesis, so it does not wait for B); and everything this plan says
about the entry side comes from READING an unfolded `ldInv`, never from
building one. Building it is how we find out whether that analysis holds. The
back edge falsified a read-off-the-goal guess twice in one day.

**3. A1 + A2, batched.** Pure hygiene, both touch the contract record, both
need a full gate. One gate run, not two. No dependency either way, so they go
where convenient — here, before B, which touches the same area.

**4. B — memory addressing.** Informed by spike (b) and by what D3 actually
turned out to need.

**5. C1, C2, C3, then D1, D2.** D2 must follow B: if B1 changes the cell
vocabulary, a cell-trade tactic written first gets rewritten.

**6. E.**

Then F, in whatever order the work at the time demands; F1 and F2 are the two
worth doing.

**Risk notes.** B is the only phase changing the trusted statement surface — it
needs the gate and a deliberate look at what it means for existing end
theorems. C2 is the largest single piece of real work. Every phase touching
`Contracts.v`, `mem_full_spec` or the generators needs a full rebuild and the
gate behind it (~45 min on this box at GATE_JOBS=1).
