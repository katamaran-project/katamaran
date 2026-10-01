# PLAN-chunk-facts: pure facts implied by a chunk, assumed when it is produced

Status: REVERTED 2026-10-01 (implemented, measured, not kept; patch in
`plans/chunk-facts.patch`).  See the 2026-10-01 log entry first.  Was: DESIGN (2026-09-30). Motivating case: the parametric-mlen muladd probe
D0 (`Example/ZZArrD0.v`, `PLAN-bv-arith-solver.md` U5), a loop that stops on a
POINTER compare.  Its exit needs `t0 - 4 = dp - 4c`, which is exactly the fact
`e = a + s*n` inside `interp_arr` (`IrisInstanceBinary.v:205`), invisible to the
symbolic executor because an `arr` chunk is opaque to it (`Sig.v:96`: "stated
only in the Iris interpretation").

## What exists (surveyed 2026-09-30, this branch and upstream `main`)

No mechanism turns a chunk into pure facts.  The per-predicate knobs are
`𝑯_is_dup` (spatial only), `𝑯_precise` (asserts output equalities on consume;
obligations, not learned facts) and `SolverKit.solver` (formulas only, never the
heap; RiscvPmp's `simplify_user` has every clause commented out).
`produce_chunk` is `pure (cons (peval_chunk c) h)` on both branches.

## Design

Two parameters, split by the Formula dependency (`Formula` is defined after the
predicate kits):

1. `HeapPredicateKit` (`Syntax/Predicates.v`): the CONCRETE facts
   `𝑯_facts : forall p, Env RelVal (𝑯_Ty p) -> Prop` (default `True`), plus in
   `PredicateDef` the Iris obligation
   `lfacts : luser p ts ⊢ ⌜𝑯_facts p ts⌝ ∗ luser p ts`.
2. `SolverKit` (`Symbolic/Worlds.v`): the SYMBOLIC facts
   `user_chunk_facts : forall Σ p, Env (Term Σ) (𝑯_Ty p) -> PathCondition Σ`
   with a ONE-WAY spec `𝑯_facts p (inst ts ι) -> instprop (user_chunk_facts ts) ι`.
   One-way is exactly what refinement needs (concrete assume P ≥ symbolic
   assume S iff P → S), and lets `DefaultSolverKit` supply `[]`.

Executor: `SPureSpec.produce_chunk` assumes `chunk_facts c` (user chunks via
the kit; `ptsreg`/`wand` none; `conj` both) and SKIPS the assume when the list
is empty, so register reads (which re-produce a `ptsreg` chunk every step) pay
nothing.  `CPureSpec.produce_chunk` assumes the concrete counterpart.

Proof sites (only built files):
- `Shallow/Monads.v`: `produce_chunk`, `mon_produce_chunk`, `wp_produce_chunk`
  (the ONE Iris-level lemma every produce soundness proof goes through; its
  proof now uses `lfacts`).
- `Symbolic/Monads.v`: `produce_chunk`, `pext_produce_chunk`.
- `Refinement/Monads.v`: `refine_produce_chunk` (+ its uses at :1485/:1512).
- `Iris/BinaryWeakestPre.v`: new `IrisPredicates2` parameter `lfacts_inst2`.
- `CFGVer/VerifierRel.v:2885`: `sound_exec_instruction` unfolds
  `CPureSpec.produce_chunk` by `cbv`.
- RiscvPmp: `Sig.v` defines both facts for `arr`
  (`secLeak a ∧ secLeak n ∧ secLeak e ∧ e = a + s*n`; `interp_arr` is `False`
  unless all three are `SyncVal`), `IrisInstanceBinary.v` proves `lfacts`.

Not built, not touched: `LaterBinaryWp.v`, `Staging/`, `MinimalCaps`, `test/`.

## Phases

1. Framework parameters + defaults, executor + refinement + shallow soundness,
   RiscvPmp with `𝑯_facts := True`/`[]` (behaviour unchanged). Full rebuild.
2. RiscvPmp `arr` facts + `lfacts` proof. Full rebuild.
3. D0: invariant gains the count bound `c < 2^30` (user decision: bound from
   the loop invariant, not from `interp_arr`); re-run D0, Sym4, Sym6.
4. Measure: cost on the gate examples (extra assumes), docs.

## Log

### 2026-09-30: phases 1+2 implemented, full rebuild running

Landed as designed, with three deviations worth knowing:
- `SolverKit`/`DefaultSolverKit` now `Import B` and `P` (they did not, so
  `𝑯`/`Term` were out of scope for the new parameter).
- CONCRETE `produce_chunk` matches on the chunk: registers and wands stay a
  bare `pure`, so the register read/write refinement and soundness proofs
  that `cbv` through it see the old shape.  `refine_produce_chunk` normalises
  the concrete side first with `refine_purespec_mono`.
- The Iris lemma `interpret_scchunk_facts` lives in `Shallow/Monads.v`
  (own section, local proofmode import), not `Chunks.v`, which has no
  proofmode and should not get one.
Refinement: new `RPathConditionImp` (one-way), `chunk_facts_sound`,
`refine_chunk_facts`, `refine_assume_pathcondition_imp` (a copy of the iff
version's proof: it only used the concrete-to-symbolic half).
RiscvPmp: `arr` facts are `secLeak a/n/e` + `propeq e (a + of_Z s * n)`.
Compiled through `IrisInstanceBinary.vo`.  D0's invariant gained
`c <u 2^30`.

### 2026-09-30: phase 3 -- D0 passes; IA/KA/MA regressed, fixed by n-ONLY invariants

- Full rebuild green after one fix (`VerifierRel.sound_exec_instruction`
  unfolds the concrete `produce_chunk` of the prologue's `ptstoinstr` chunk:
  its facts are `True`, `specialize (Hverif I)`).  D0 passes (8 s): the arr
  fact gives `t0 - 4 = dp - 4c`, its invariant's `c <u 2^30` the rest.
  Sym4 passes (228 s).
- IA/KA/MA regressed, one leaf each.  Mechanism (VC dump of MA): the
  invariant named the array end with its OWN variable `e` next to the
  current pointer `bp` and count `n` -- three variables for two degrees of
  freedom, the relation `e = bp + 4n` hidden in `interp_arr`.  The exit
  (`bp + 4 = e`) used to rename `e := bp + 4`, so the post's `arr [e; c; e]`
  matched by START ADDRESS without anyone knowing the count reached 0.  With
  the fact, `e := 4n + bp` is substituted first, the exit arrives as
  `4 + bp = 4n + bp` (no bare variable), and the start-address match fails on
  spelling.  I.e. the old proofs passed for a superficial reason.
- Fix (Emiel: "the only real variable is n"): restate the loops with the
  remaining count `n` as the ONLY varying logic variable; every address is
  FIXED END - 4n.  The post names everything by the remaining count at exit
  `c` (bound to n - 1 by the angelic array match) plus `c = 0` as a pure
  obligation, so no chunk key depends on knowing n = 1.  Template
  `Example/ZZArrLoopN.v`; instances ZZArrMN (hand-written), ZZArrMT, ZZArrIN,
  ZZArrKN: all Qed first try, no closer changes (22.6 / 31.7 / 21.4 s vs
  ~4-10 s for the old ones -- the extra angelic array matches, unmeasured).
- Tail rewired to them as `ZZMbTailN.v` (the post-loop `clem_arr_lockstep`
  is gone: the new posts state both pointers).

### 2026-10-01: REVERTED -- n-only invariants make it redundant

- The hook ASSUMED facts (it never created obligations), but the arr fact
  `e = a + s*n` has a bare variable on one side, so the solver SUBSTITUTED it
  and respelled terms: that, not the knowledge, broke IA/KA/MA.  A variant
  that keeps facts as knowledge only (unoriented, e.g. `e - a = s*n`) was
  never built.
- With invariants that name every address from a FIXED END and the remaining
  count (Emiel: "the only real variable is n"), the relation is stated in the
  invariant: D0 restated that way (`Example/ZZArrD0N.v`) passes WITHOUT the
  hook (12.8 s), as do the I/K/M template loops (ZZArrLoopN.v).
- CORRECTION: `PaddedLoopResult.v` running out of memory was blamed on the
  hook (and before that on a `replay` pipeline change, also reverted).  Both
  were wrong: the file needs ~9.4 GB resident at the COMMITTED state and was
  killed by `ulimit -v` 10-14 GB (U4 built it under 20 GB).  `ulimit -v`
  caps VIRTUAL memory, which runs well above resident for Rocq.  The file was
  then migrated to the ai_loop block style (27 s / 7.3 GB).
- Separately measured and also reverted: `cfg_postprocess = postprocess o
  replay o postprocess` in the VC pipeline.  On KN it cut 9 residual asserts
  to the 3 real ones (the rest were ring identities left by postprocess's
  late evar substitution) at +1% construction, but it was adopted on an
  unmeasured hypothesis about the tail's memory.  Re-measure before reviving.
