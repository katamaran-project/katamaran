# PLAN: bitvector arithmetic in the solver (ranges + linear normal forms)

Status (2026-11-05): REVIVED as PLAN-rsa O5(a), branch `issue/solver-o5`
(worktree `../katamaran-relval-rsa`). DRAFT, awaiting Emiel's review of the
revision at the END of this file ("REVISION 2026-11-05"), which supersedes
every "Phases" section above. History: the ring canonical forms in peval
(U1-U5 below) landed, then were re-done on the RelVal pair model (relval-pair
R1, f0d4080d); the solver-level DECISIONS and the RANGE layer were never
started.

Original status: PROPOSED 2026-09-29. Emiel chose this ("try b first")
over a post-hoc lowering lemma (a) for the ZZMbClose closer.

## Why

At symbolic mlen (PLAN-array-invariants, parametric muladd) every VC residual
the post-hoc closer `ZZMbClose.solve_mb_vc` handles is one of:

| residual (as seen in the finished VC) | kind |
|---|---|
| `(-1 + M) & 0x3fffffff = -1 + M`, `S0 = s + 4` from a masked count | propeq, mask under a range |
| `(b + 63) >> 5 = M + 1` (K/M bounds from `x[0]`) | propeq, shiftr of a constant offset |
| `-3 + M = -2 + c`, `k + c = 1 + k` with `c = 1` known | propeq, linear |
| `63 + sext b <u 64` with `31 <u sext b`, `sext b <u 65536` in `wco` | relop, DEAD branch |
| `v0 = v0 + (M << 2)` | propeq, DEAD branch (nonzero difference) |

`M = (31 + sext b) >> 5`, `b` public with range facts in `wco`.

None of these is decided during execution, because the solver has no
arithmetic beyond pattern rules (`try_bvadd_cancel*`, `try_fetch_bound`).
So they survive to the end: equalities as residuals the closer must lower
from `RelVal` to `bv` to `Z` (the destruct/injection/spelling zoo), and dead
branches as whole subtrees carried to the end -- part of why the whole-function
VC did not fit in memory.

## What

A decision procedure inside the solver, used by `simplify_relop` (eq, neq,
bvult, bvule, bvslt?, bvsle? at `ty.bvec n`) and the `formula_propeq` arm:

1. **Linear normal form mod 2^n.** `lin : Term Σ (bvec n) -> LinForm`, where
   `LinForm = Z * list (Z * atom)` means `c + Σ kᵢ·aᵢ (mod 2^n)`. Built
   structurally: `term_val` -> constant, `bvadd`/`bvsub`/`negate` -> sum,
   `shiftl t (val k)` and `bvmul (val k) t` -> scale. Everything else is an
   ATOM (a normalised subterm, compared by `Term_eqb`). These are ring
   identities mod 2^n: they hold on each world of a `RelVal` separately, so
   they need NO range and NO publicness (relval-rewrite-over-secrets).
2. **Ranges.** `range : wco -> Term -> option (Z * Z)`, unsigned bounds. Seeds:
   `wco` facts `c <u t`, `t <u c`, `c <=u t`, `t <=u c`, `t <> 0`. Structure:
   constants; `bvadd` without wrap; `shiftl`/`shiftr` by a constant; `land`
   with a constant; `sext`/`zext` at equal width (identity).
3. **Range-conditional atom rewrites** (these need ranges, so they are only
   applied to terms whose variables carry range facts -- such facts are
   relops, which are `False` at a `NonSyncVal`, so those variables are public):
   - `land t (2^k - 1)` = `t` when `range t ⊆ [0, 2^k)`;
   - `shiftr t k` with `lin t = q·2^k + r + L` = `q + shiftr (r + L) k`, when
     `t` and `r + L` do not wrap (floor((2^k q + R)/2^k) = q + floor(R/2^k));
   - `sext t` at equal width = `t` (a peval rule, arguably).
4. **Decisions.**
   - propeq / eq: equal normal forms -> discharge (`Some empty`); forms
     differing by a constant `d` with `d mod 2^n <> 0` -> refute; difference
     `d + L` with `range(d + L)` excluding 0 mod 2^n -> refute.
   - bvult / bvule: disjoint or ordered ranges -> discharge or refute.
   - neq: the dual of eq.
   Everything else falls through untouched (never `error` for "cannot decide").

## Soundness

- Z-level core: `lin` evaluates to the term mod 2^n; `range` soundness under
  `instprop (wco w)`; the two conditional rewrites. Pure `bv`/`Z` lemmas,
  developed in preamble mode.
- `RelVal` lift: normal-form equalities are ring identities (both projections,
  no case split). The conditional rewrites use ranges that come from `wco`
  relops, which force `SyncVal`. relop DISCHARGES need publicness of the
  operands: from the same range facts, or `secLeakT` (as `try_bvadd_cancel`).
- Hooked through the existing `simplify_relop_spec` / propeq arm spec, so
  `SolverSpec` carries it downstream with no other proof touched.

## Where

A new `theories/Symbolic/BvArith.v` for the `{Σ}`-generic pieces
(`LinForm`, `lin`, the rewrites, the Z lemmas), included the way
`PartialEvaluation.v` is, and the `{w}`-level hooks (they need `wco`) in
`Solver.v`'s `GenericSolver`, next to `try_fetch_bound`.

## Phases and gates

- **P0 -- shapes.** Dump the real formulas (propeq/relop, operand order, width
  spellings, whether `sext` survives peval) from small probes for each row of
  the table. Gate: the table above, restated in the exact solver-input form.
- **P1 -- Z core in preamble.** `LinForm`, `lin`, `range`, the rewrites, with
  proofs. Gate: `vm_compute` self-tests on every row (positive AND negative:
  a satisfiable formula must never be refuted).
- **P2 -- hooks + spec.** One `Solver.vo` build. Gate: full `Results.vo`
  rebuild green (every existing example unchanged), then the gate script.
- **P3 -- payoff.** Re-run D/D0/I/K/M, the tail and the caller with the
  closer reduced to `solve_param_vc` (+ at most the ∃ case). Measure the
  whole-function VC's memory before/after. Gate: `valid_sym6` by the generic
  closer alone, negative controls still fail.

## Risks

- `Equations` and bvec widths (core-executor-internals rule 6): keep the
  recognisers returning non-dependent data.
- Cost: the range scan is O(|wco|) per bvec relop/propeq; gate it behind a
  cheap syntactic test (the term contains a shiftr/land/relop-able shape).
- Normal-form spelling vs peval's: `lin` is used only to DECIDE, never to
  rewrite the terms the executor keeps, so peval's normal form is unaffected.

## Progress log

### P0 DONE (2026-09-29) -- the shapes, probe `Example/ZZBvA0.v`

Exact solver input (M = `(31 + sext b) >> 5`; `sext b` SURVIVES peval; the
range facts are `formula_bvult (val c) (sext b)`, `formula_bvult (sext b)
(val c)`, `formula_neq (sext b) 0`, i.e. stated on the ATOM `sext b`):

| row | formula |
|---|---|
| masked count (angelic match) | `formula_propeq (x + (M<<2)) (4 + (x + ((-1 + M) & 0x3fffffff) << 2))` |
| `(b+63)>>5` (angelic match) | `formula_propeq (4 + (x + (M<<2))) (x + (((63 + sext b) >> 5) << 2))` |
| dead bltu (assume) | `formula_bvult (63 + sext b) 64`, other side `formula_bvule 64 (63 + sext b)` |
| dead beq (assume) | `formula_propeq x ((M<<2) + x)`, other side `formula_neq x ((M<<2) + x)` |

Two findings on the way:
- A READ at a differently-spelled address is not a residual at all: the
  read's chunk match is syntactic (post-peval), with no arithmetic fallback,
  so it is a hard `SymProp.error`.  This procedure helps FORMULAS only
  (angelic chunk matches, branches); reads still need one spelling (peval).
- **`RelVal` equality is NOT "both projections equal".** `liftBinOpRV` is
  `SyncVal` only when both operands are, so `NonSyncVal v v <> SyncVal v`,
  and `x - x = 0` is FALSE for a secret `x`.  So a normal-form equality
  discharges a `propeq` only when both sides have the same NON-PUBLIC
  variables; refutation needs one projection only.  (The
  `relval-rewrite-over-secrets` skill states the projection claim outright;
  it is wrong in this corner -- rewrites that drop or add a variable.  To fix
  there, and to check whether any existing peval rule drops a variable.)

### P1 design decisions

- Matching: `Equations` one-clause head matchers returning a NON-dependent
  view (`VAdd a b | VSub a b | VNeg a | VShl a k | VMulC c a | VVal v |
  VAtom`), and FUEL-bounded recursion falling back to an atom (sound by
  construction) -- no structural recursion through `Term_bvec_case`.
- `sext` stays an ATOM: the range facts are stated on `sext b` itself.
- `term_relval` is an atom that blocks any DISCHARGE (it may be NonSyncVal).

## REVISION 2026-09-30: Emiel chose OPTION 1, ring forms only (supersedes "What")

The range-conditional rewrites above were ad hoc (cut to the P0 table,
syntactic atom matching via a rebuild that had to reproduce peval's spelling).
Replaced by CANONICAL RING FORMS IN PEVAL; the solver-level range layer
(`>>`, `&`, dead branches) is deferred until phase 1 is measured.

History that matters: upstream Katamaran HAD ring canonicalisation of
bitvector terms (`TermRing_bv`, `Ring_polynom` `norm_aux`, commits 29d965c0,
48c1d3b2, fa563609).  This fork DISABLED it in 196eae12 ("disable most of
peval, most ring lemma don't hold anymore"): its `ring_theory` is modulo
`≡` = RelVal equality, and `x + (-x) ≡ 0` is false for a secret x.

Foundation (what does hold): two ring-fragment terms are RelVal-equal iff
(1) both PROJECTIONS are equal -- ring identities mod 2^n, per projection
(`ZZBvCore.lin_sound`, proved) -- and (2) they agree on SyncVal-ness, which
for lifted ops means: the same set of ATOMS occurs.  So:

- Decisions (Emiel): a cancelled atom KEEPS coefficient 0 (`x - x` becomes
  `0 * x`), so (2) is preserved; atoms are ordered by a STRUCTURAL comparison
  (variables by context position, then operator tag, then arguments;
  unorderable subterms are equal-or-unordered).
- The order needs NO correctness proof: merging uses Term_eqb, and reordering
  a sum never changes its value; the order only decides canonicity.

### Phases (replaces P1-P3 above)

- **R1 -- order + canonical form** (scratch `Example/ZZBvCore.v`, reuses
  parts 1-2: `lin`, `lin_sound`, merge): `term_cmp`; `canon t` = lin, merge,
  sort, coefficients mod 2^n (zeros kept), rebuild.  Rebuild convention,
  chosen to keep today's prevalent shapes: constant LEFTMOST, right-nested
  sum, coefficient 1 -> `a`, 2^j -> `a << j`, else `bvmul (val k) a`.
  Gate: `inst (canon t) = inst t` (RelVal, both halves above) + vm_compute
  self-tests (the neighbour pair, x - x, commuted sums).
- **R2 -- peval integration** (`PartialEvaluation.v`): the bvec ring ops go
  through `canon`.  Gate: `peval_sound` still proved; full `Results.vo`.
- **R3 -- fallout**: solver rules and closers that match old shapes
  (`try_bvadd_cancel*`, `try_fetch_bound`, `solve_symbase_fetch`'s
  `relval_fetch_*`), all examples, the gate script.
- **R4 -- measure**: the muladd probes; which residual kinds remain.

### R1 DONE, R2 DONE (compiles) 2026-09-30

- R1 (`Example/ZZBvCore.v`, no admits): `canon_term t := rebuild (canon_lf
  (lin 64 t))`, `canon_sound : inst (canon_term t) ι = inst t ι` EXACTLY over
  RelVal, via `relval_ext` (SyncVal-ness + both projections), `lin_sync`
  (SyncVal iff every atom is), `lin_sound` (projections mod 2^n).  The view
  also reads `bvmul (val c) a` (so rebuilt terms re-linearise to themselves)
  and the rebuild spells coefficient -1 as `negate a` (the mask recognisers
  match `negate (bvand h 1)`).  Self-tests: neighbour pair one term; x + y =
  y + x; (M<<2) + x = x + (M<<2); 4 + (x - 4) = x; x + 4 <> x; 3x + x = x << 2;
  idempotent; the mask shape unchanged; x - x = `0 * x`.  The canonical
  spelling matches today's prevalent one (`x + (M << 2)`, `4 + (x + ...)`).
- R2: the core ported verbatim into `PartialEvaluation.v` before `Section
  WithLCtx` (RelVal valuation notation `RValuation`: the file's own
  `Valuation` notation is Val-based, an upstream leftover); `peval_bvadd`'s
  catch-all, `peval_shiftl` (constant amount), and new `peval_bvsub` /
  `negate` arms go through `canon_term`.  The two ad-hoc rules of 23f904fa
  (constant floating, << distribution) are subsumed and their self-tests
  removed (they now live, concrete, in ZZBvCore).  Builds in 41 s.
- Port traps: SSReflect `rewrite` could not infer a list argument inside the
  functor (give the instance); `cbn` unfolded `lf_modk` in the goal only
  (unfold it everywhere first); Znat/Nnat/Zdiv/Permutation imports.
- R3 running: full Results.vo rebuild with `-k`.

## REVISION 2026-09-30 (later): port to main's mechanism (Emiel)

R3 came back CLEAN (full Results.vo rebuild green with canon_term wired in,
no fallout).  Emiel then chose to reuse the upstream machinery, and after
reading `main`: REINSTATE main's `peval2` (not just swap the normaliser).

What main has (unchanged in essence since the fork, merge base 2025-08-01;
Dominique, fa563609/b226c5d9/98916b52, June 2025): `peval t =
CanonTerm_to_Term (peval2 t)` for all but vars/vals/cons.  `peval2` quotes
bvadd/bvsub/bvmul (and int plus/minus/times) into Ring_polynom `PExpr`s,
every other op is `peval`'d and quoted as an ATOM (numbered by first
occurrence, Term_eqb); `CanonTerm_to_Term` = `norm_aux` + `Pphi_dev`.
This branch still carries that code, commented out.

Gaps against our needs, each to be closed:
1. Soundness is single-world (`ring_theory` modulo ≡, false over RelVal).
   -> per-projection argument + ATOM-SET CHECK: if `norm_aux` drops an atom
   (x - x -> 0), re-add it as `0 * a`, so SyncVal-ness is preserved.
2. Atom order = first occurrence: `x + y` and `y + x` stay different.
   -> sort the atom environment by the structural key, renumber the PExpr.
3. `<<` by a constant is an atom.  -> quote it as `PEmul (PEc 2^k)`.
4. (main is nonlinear -- kept.)

Phases:
- U1 (scratch, like ZZBvCore): the RelVal-sound normaliser --
  (a) projection of `evalPExprTm`/`evalPolTm` = the Val-level PEeval /
  Pphi_dev (comProj lemmas; peval_binop'_sound); (b) Val-level correctness
  from Ring_polynom's `norm_aux_spec`/`Pphi_dev_ok` at the plain bv/Z ring
  (`bv.ring_theory` holds per projection); (c) SyncVal-ness = all atoms of
  the polynomial's variables; (d) the atom-set check + padding.  Gate:
  `inst (canon p env) ι = inst (evalPExprTm env p) ι` exactly, no admits.
- U2: env sorting + renumbering; `<<`-by-constant quoting.  Gate: the
  ZZBvCore self-tests restated (neighbour pair, commuted sums, 3x + x,
  x - x = 0 * x, idempotence, mask shapes untouched).
- U3: reinstate peval2/CanonTerm/peval in PartialEvaluation.v, merged with
  this fork's rules: non-ring ops go through the fork's peval_binop/unop
  (mask algebra, coalesce, mulx) and are quoted as atoms; bvadd's mask
  clause (`peval_bvadd_mask`, `zext b + ones` -> expand) must still fire, so
  it is tried before quoting.  Retire the interim canon_term.  Gate:
  PartialEvaluation.vo + peval_sound.
- U4: full rebuild, fallout, gate script.
- U5: measure muladd (R4 of the previous revision).

### U1 design, refined (2026-09-30): reuse upstream's PROOF with a weaker setoid

- Upstream proves `evalPol_norm_aux` by instantiating Ring_polynom's generic
  `norm_aux_spec` / `Pphi_dev_ok` over terms modulo `≡` -- false over RelVal.
  Instantiate the SAME lemmas modulo `teq side` ("equal on projection side":
  `∀ ι, proj side (inst t ι) = proj side (inst u ι)`): an equivalence, a
  congruence for every op (all ops are `liftBinOp`/`liftUnOp (eval op)`,
  checked in BinOps.v/UnOps.v), and the ring axioms DO hold modulo it (each
  projection is a plain bv/Z ring).  So `norm(t) ~side t` for both sides,
  with upstream's proof structure.
- SyncVal-ness by a COMPUTABLE CERTIFICATE, not by reasoning about Pphi_dev:
  since every op lifts, a term is SyncVal iff all its LEAVES are (a general
  lemma by induction over binop/unop, leaves = everything else).  After
  normalising, compare the leaf sets of input and output (Term_eqb); pad any
  dropped leaf back as `0 * a`.  Both projections equal + same leaves =
  exact RelVal equality.

### U1 + U2 DONE in scratch (`Example/ZZBvRing.v`, no admits), 2026-09-30

- `norm_teq`: upstream's `norm_aux` + `Pphi_dev` correct modulo `teq side`
  (both sides), from Ring_polynom's own `Pphi_dev_ok` / `norm_aux_spec`
  (instances built explicitly with `@`; SSReflect `rewrite` cannot do the
  setoid step, it unfolds `teq`).  Needs `bv_term_ring` / `_eq_ext` /
  `_morph` modulo teq, `teq_equiv`, and Proper for term_binop/unop.
- Leaf certificate: `leaves`, `sync_leaves` (every op lifts, so SyncVal iff
  all leaves are; one induction over Term), `leaf_eqb` (Ty eq_dec +
  Term_eqb), `same_leaves`, `teq_leaves_inst` (both teq + same leaves =>
  exact RelVal equality).
- `canon_with env p t := let u := clean (pad env (evalPol env (normZ p))) in
  if same_leaves t u then u else t`; `canon_with_sound` exact.  `pad` re-adds
  an env atom the normal form lost as `0 * a`; `clean` removes literal
  `+ 0`/`* 1` that Pphi_dev leaves and moves a literal constant LEFT (the
  solver's rules expect `c + s`).
- `canon_term`: quote (`<<` by a constant quoted as `* 2^k`), collect atoms,
  SORT by structural key, re-quote with the sorted list as the starting env
  (no permutation lemma), `canon_with`.  `canon_term_sound` exact.
- Self-tests pass: neighbour pair one term; x + y = y + x; (M<<2) + x =
  x + (M<<2); 4 + (x - 4) = x; x + 4 <> x; 3x + x = x << 2; idempotent.
  Shapes: `4 + (x + 4 * M)` (NB `4 * M`, not `M << 2`: Pphi_dev's
  spelling, as on main), `x - x` -> `0 * x`, `x - y` -> `-y + x`, mask shape
  `negate (bvand b 1)` unchanged.

### U3 design choices

- main's `TermRing` requires `ring_theory` modulo ≡: change the class to
  carry the ops plus the teq-ring facts; the RQuote / Term_Quote_* lemmas only
  use the ops and ≡-properness (exact reconstruction), so they carry over.
- `CanonTerm_to_Term ct := canon_term (evalPE env p)` (reconstruct, then the
  sorted re-quote above) -- keeps main's peval2 island structure.
- The fork's `peval_bvadd_mask` (`ones + zext b` -> expand) runs on the
  canonical output (`c + a` shape), so the mask algebra keeps firing.
- INT is left OUT of the ring for now (main quotes plus/minus/times too): the
  solver's int rules match specific shapes (`int_bound_shape` =
  `L - (K + unsigned s)` for try_fetch_bound).  bvec first, int later.

### U3 DONE (PartialEvaluation.vo builds, no admits), 2026-09-30

- The interim linear canon core is REPLACED by the ZZBvRing core (teq ring
  instances, `norm_teq`, leaf certificate, clean/pad, quote, sorted
  `canon_term`), ported verbatim (`Valuation` -> `RValuation`; the copied
  BinList helpers dropped for the file's own Util versions).
- `TermRing` carries OPS ONLY (its ≡ ring fields are unprovable over
  RelVal); `TermRing_bv` instance; the ≡-based `evalPolTm` /
  `evalPol_norm_aux` / `tmr_ring_*_peval'` / `Pphi_more_proper` removed.
- main's `peval2` / `CanonTerm` / `CanonTermRep` / `CanonTerm_to_Term` /
  `peval` / `peval_sound` reinstated.  CanonTerm is bvec-only (int = Term).
  `peval2_binop` / `_unop` use a CONVOY match: ring ops quoted
  (`Term_Quote_bin` PEadd/PEsub/PEmul, `Term_Quote_unop` PEopp), `<<` by a
  constant quoted as `* 2^k` (`quote_shiftl_valid`, exact over RelVal), every
  other op one generic default (normalise children, the fork's
  `peval_binop`/`peval_unop` -- mask algebra, coalesce, mulx -- quote the
  result as an atom), so ONE soundness lemma covers them.  `term_relval`
  (fork-only constructor) is quoted as an atom.
- `CanonTerm_to_Term` = `post_mask (canon_term (evalPExprTm env p))`:
  post_mask applies `peval_bvadd_mask` to a `c + a` result, so the mask
  algebra's `ones + indicator` rule still fires.
- Traps: `{| ... |}` could not infer σ for the TermRing instance (use the
  constructor); `destruct op` puts shiftl BEFORE bvadd (make the case script
  order-independent with `first`); an `inst_val` stated at `RV (Val σ)` does
  not rewrite goals spelled `RelVal` (pin the eq type).
- U4 running: full Results.vo rebuild (-j1 -k).

### U4 done (2026-09-30)

Full `Results.vo` rebuild with the reinstated `peval2` passed with no fallout:
97 files, `-j1`, 3597 s wall, 8.6 GB peak RSS. The new spellings (`4 * M` for
`M << 2`, constants on the left, sorted atoms) broke no solver rule and no
example's closer. Gate steps 1–2 (build, hole scan) passed. The axiom probes
(step 3) were skipped at the user's request. Next: U5 (re-measure the muladd
probes with the closer reduced).

### U5 measured (2026-09-30): what reaches the closer after ring normalisation

Census (`Example/ZZMbCensus.v`, an instrumented `solve_mb_vc`) on the parametric
muladd probes:

| probe | goals after `solve_vc` | arithmetic leaves | trivial leaves |
|---|---|---|---|
| IA, KA, MA | 0 | 0 | 0 |
| DAng | 1 | 1 (`v2 + v1 = 1 + v2`, closed from hypotheses) | 0 |
| Tail | 3 | 7 | 4 |

Tail's 7 arithmetic leaves all concern the word count `M = (31 + b) >> 5`, and
NONE is a ring fact: two are `4 * M <> 0` (needs the range `1 <= M <= 2048`),
one is the shift identity `4 * ((63+b)>>5) = 4 + 4 * ((31+b)>>5)` (needs
`b >= 32`), and four are dead branches refuted from hypotheses.  So every
remaining residual is `shiftr` + ranges, i.e. the deferred range layer.

Fallout: the tail FAILED on the new `peval` until the closer learned `bv.mul`
(`bv.unsigned_mul` in `bv_lin_rw`; `bv.mul` kept folded in `rv_leaf`'s cbn),
since `M << 2` is now spelled `4 * M`.  Cost: tail stages 224 s vm_compute,
26 s solve_vc, 10 s closer (~260 s user); ~220 s before the port, within
noise (one run said 395 s user and did not reproduce).

Still open: D0 fails on `SyncVal (v3 + v2) = SyncVal (1 + v3)` with only
`v2 <> 0` known -- its exact-count invariant, pre-existing, not the port -- and
blocks Sym4 / Sym6 (the whole-program caller), which import it.

## REVISION 2026-11-05: O5(a) -- solver decisions, isolation, ranges + closer hardening (DRAFT)

Supersedes every "Phases" section above. Driven by PLAN-rsa O5 (see its §5
rows of 2026-11-05 for the measurements).

### Why now

- **Elimination.** In montymul's 4-unrolled loop, `mm_bounds` with
  `k = T + (-1)·c` eliminates the wrong existential. `try_isolate_inner` is
  guarded by `secLeakT s`, and c's publicness fact (`c = R`) is produced after
  `mm_bounds`, so the bare parameter T is substituted instead. Stopgap in use:
  orient the equation `T = k + c` by hand (cfgver-contracts STOPGAP rule).
- **Dead branches reach the closer.** With the reoriented contract,
  `valid_mmq_loop` went from 361 s to more than 1800 s.
  - The wrong branch's first leaf is the block-exit pc equation
    `q = 0x180 + q`, which is false from its syntax alone.
  - The solver does not decide it: `bvadd_cancel_pair` needs a `bvadd` on
    both sides.
  - The closer refutes it with `bv_lin` over the whole context: 430
    hypotheses, 58 quotient/remainder variables, and lia over 60 s.
  - A TRUE leaf also spends about 17 s of its 17.2 s translating irrelevant
    hypotheses.
- **Emiel 2026-11-05.** Do the whole plan (decisions plus ranges) and harden
  the closer: a precheck, then a relevance filter with fallback. The solver
  work goes off KatamaranRel, the closer work on the RSA branch. "Cover our
  bases": fix the general mechanism, not the montymul instance.

### What the pair model changed (makes the earlier sections simpler)

- **Equations reduce to a difference.** RelVal is a pair, and terms are a ring
  modulo ≡ again (main's `TermRing`, `canon_term` proved,
  `PartialEvaluation.v:521`). So `l = r` (propeq) holds iff
  `l + (-1)·r ≡ 0`, per projection. No SyncVal-ness side condition, no padding,
  no leaf certificate. The note above "RelVal equality is NOT both
  projections" is OBSOLETE.
- **Ranges need no publicness.** `formula_relop` is pointwise (relval-pair
  D3): `a <u b` means it holds in both projections. A range fact from `wco`
  therefore holds per projection, for public and secret atoms alike, and no
  decision needs publicness.
- **The isolation guard is only a cost filter.** relval-pair-baseline/AUDIT.md
  says so for `try_isolate_inner`'s `secLeakT` guard: `relval_isolate` is a
  pointwise equivalence.

### Components

S = solver (`issue/solver-o5`, `theories/`). C = closer (`issue/rsa-montymul`,
`Example/Muladd/MuladdParamClose.v`).

- **S1 linear decision.**
  - `lin_diff t1 t2 := canon_term (t1 + (-1)·t2)` reuses peval's canonical
    form; there is no second normal form.
  - It is hooked in FIRST in the `formula_propeq` arm of `simplify_formula`
    and in `simplify_relop`'s bvec `eq`/`neq` arms (Solver.v ~3140, ~3946).
  - A constant 0 discharges (eq) or refutes (neq), a nonzero constant does the
    opposite, anything else falls through unchanged.
  - Decides `q = 0x180 + q`, `x + 4 <> x`, and the P0 row `v0 = v0 + (M<<2)`
    up to the nonzero part (that row needs S3).
- **S2 isolation (a1 + a2).** Replaces `try_isolate_aux`'s pattern.
  - From `lin_diff t1 t2 = c + Σ kᵢ·aᵢ`, pick the INNERMOST variable atom x
    whose coefficient is ±1 and which occurs in no other atom.
  - Emit `x = ∓(c + Σ_{other})`.
  - No `secLeakT` guard (AUDIT). With no such x, fall through.
  - Must stay BEFORE `try_bvadd_cancel_val_propeq` (the 2026-10-22 ordering
    note at Solver.v ~3596).
  - Covers the caller's instantiation `T = u + cx`, not only a bare
    parameter.
- **S3 ranges.** `range (wco w) t : option (Z * Z)` gives unsigned bounds per
  projection.
  - Seeds: `wco` relops of an atom against a constant (`<u`, `<=u`, both
    sides), `a <> 0`, `a = c`.
  - Propagation through structure:
    - constants;
    - `c + Σ kᵢ·aᵢ` when no wrap is possible;
    - `>>` and `&` by a constant;
    - `zext`, and `sext` at equal width.
  - Decisions:
    - `bvult`/`bvule` and their negated forms: discharge or refute on ordered
      or disjoint intervals;
    - eq/neq/propeq: refute or discharge when the range of `lin_diff`
      excludes 0. Examples: `4·M <> 0` from `1 <= M <= 2048`, RsaCcopyGate's
      six `k + 4·ml <> 0` leaves, the Tail census's four dead branches.
  - The old step-3 conditional rewrites (`land` mask = t, the `shiftr` split)
    are used only INSIDE a decision, never written back into terms (D1).
  - Cost: a scan of `wco`, O(|wco|), run only when S1 fell through on a bvec
    formula.
- **S4 closer hardening (C).** In `rv_leaf` / `bv_lin`:
  - **Precheck.** Before any bv_lin alternative, if the NEGATED goal follows
    from an empty Prop context (bv variables and their bounds kept), fail the
    leaf at once. This catches every ground-decidable false leaf the solver
    never saw, for example one created when the closer itself instantiated an
    evar.
  - **Relevance filter.** Run `bv_lin` first on the hypotheses transitively
    connected to the goal through shared variables. Fall back to the full
    context only if that fails.

### Phases and gates

- **O0 shapes** (ZZ/preamble, cheap). Re-dump the solver-input forms under the
  current peval for:
  - the P0 table rows (muladd Tail, D0);
  - `q = 0x180 + q`;
  - mmq's `k = T + (-1)·c` against the caller's `T = u + cx`;
  - RsaCcopyGate's `k + 4·ml <> 0`.

  Gate: the table restated in solver-input form, each row tagged S1/S2/S3.
- **O1 core in preamble.** `lin_diff` decision, isolation chooser, `range`:
  Z lemmas plus the pair lift. vm_compute self-tests, POSITIVE and NEGATIVE:
  a satisfiable formula is never refuted, a non-entailed one never
  discharged. Gate: no admits; self-tests pass.
- **O2 hook S1 + S2** (one `Solver.vo` build, ~6 min). Specs go through
  `simplify_relop_spec` and the propeq-arm spec. Gate:
  - phase-check sentinel set + negative controls;
  - a regression file with the O0 rows, positive and negative.
- **O3 hook S3.** Same gate as O2.
- **O4 full closure on `issue/solver-o5`.** Ask Emiel first: about 70 min at
  -j1.
  - Per-file comparison against `relval-pair-baseline/rsa-final-per-file.tsv`;
    fix any fallout.
  - Then `git merge --no-ff` into KatamaranRel. The gate is disabled, so run
    the hole scan and the axiom probe by hand.
- **O5 on `issue/rsa-montymul`.**
  - Merge KatamaranRel and rebuild the RSA chain.
  - Revert the stopgaps: `mm_bounds` back to `k = T + (-1)·c`; the
    `param_eliminated` lint kept as a lint; the cfgver-contracts STOPGAP
    rule.
  - Add S4.
  - Measure `valid_mmq_loop` (baseline 361 s) and re-run the leaf-pin census.

  Gate: mmq at or below baseline; `q = 0x180 + q` no longer reaches the
  closer.
- **O6 cleanup and docs.**
  - Retire pattern rules S1/S2 subsume (`try_bvadd_cancel_propeq`, the old
    isolation) once a census shows they never fire first.
  - Update core-executor-internals' rule list, the AUDIT.md guard row, the
    PLAN-rsa O5 RESULT, and cfgver-contracts (drop the STOPGAP).

### Open decisions (DEFAULTS chosen; Emiel to confirm or redirect)

- **D1** Ranges DECIDE only; no range-conditional rewrite of terms. peval's
  spelling and every closer pattern stay as they are.
- **D2** Isolation picks the innermost ±1-coefficient variable, unguarded,
  and falls through otherwise.
- **D3** The old pattern rules stay until O6 (cheap to keep, removed on
  evidence).
- **D4** The O4 full closure runs only with Emiel's go-ahead.

### Risks

- **Fallout.** S2 fires on far more equations than today's pattern, so path
  conditions change shape. Closers matching old shapes may break (cf. R3/U5's
  `bv.mul` fallout). That is the O4 fallout budget.
- **Cost.** `canon_term` runs once more per bvec propeq/relop. Measure on
  MuladdParamVC (largest, 298 s).
- **Soundness of a wrong decision is silent** (theories/CLAUDE.md fact 4).
  The negative self-tests in O1 and the negative controls in O2 are the
  defence, plus the axiom probe at O4.

### O0 RESULT (2026-11-05)

Method: the mmq exit leaf was dumped from the real VC (probe
`Example/Rsa/ZZMmqShape.v`, untracked, on issue/rsa-montymul, `Set Printing
Depth 200` at the first top-level disjunction). The other rows were
re-normalised in a preamble (`Example.Prelude`): `peval (l + (-1)·r)` over a
one-world context with the row's atoms as variables. The P0 rows' formulas
come from the 2026-09-29 table (`Example/ZZBvA0.v`), with
`M = ((31 + b) >> 5)`.

**Finding 1: the mmq leaf is ground.** The wrong branch's first conjunct is
`eformula_propeq (eterm_var "q") (bvadd (val 0x180) (eterm_var "q"))`. Both
`q`s are the contract's base parameter (the last entry of the env), not an
existential. So the solver saw it at VC time and S1 refutes it there; the
S4 precheck is NOT needed for this leaf (it stays as a guard for leaves the
closer creates by instantiating evars).

**Finding 2: `canon_term` keeps zero-coefficient monomials.**
`peval (q + (-1)·(0x180 + q)) = 0xfffffe80 + 0·q`, not `0xfffffe80`;
`(4+q) - (q+4)` gives `0·q`, not `0`. So S1's test is "constant after
dropping 0-coefficient monomials", and S2's "occurs in no other atom" must
skip 0-coefficient atoms. The pruning goes inside `lin_diff`'s decision only:
peval's output, and with it every read spelling, stays as it is.

| row | source | `lin_diff` under current peval | true? | covered by |
|---|---|---|---|---|
| mmq exit pc `q = 0x180 + q` | VC dump | `-0x180 + 0·q` | false | **S1** (refute) |
| `x + 4 <> x` | — | `4 + 0·x` (shape as above) | true | **S1** (discharge) |
| P0 dead beq `x = (M<<2) + x` | 09-29 table | `0·x + (-4)·M` | false | S1 normalises, **S3** refutes (`1 <= M <= 2048`) |
| P0 dead bltu `63 + b <u 64` | 09-29 table | relop, not a difference | false | **S3** |
| P0 masked count `x + (M<<2) = 4 + (x + (((-1+M) & 0x3fffffff) << 2))` | 09-29 table | `-4 + 0·x + (-4)·((-1+M) & 0x3fffffff) + 4·M` | true | **none of S1–S3**: needs the mask identity as a TERM equality; interval arithmetic loses the correlation between `M` and `(M-1) & mask`. Stays with the closer (`bv_lin` reads ones-masks since 4463953f) |
| P0 `(b+63)>>5` (shift identity) | 09-29 table | — | true | **none** (closer), as above |
| mmq `k = T + (-1)·c` (k existential) | preamble | `k + c + (-1)·T` | — | **S2** isolates `k` (innermost, coeff +1, sole occurrence) → `k = T + (-1)·c`; with the caller's `T = u + cx` the same: all three atoms have coefficient ±1, `k` innermost |
| RsaCcopyGate `k + 4·ml <> 0` | preamble | `k + 4·ml` | true under ranges | **S3** (needs a lower bound ≥ 1 on `k` or `ml` in `wco`, no wrap) |
| D0 `T + c = 1 + T`, only `c <> 0` known | 09-30 rows | `-1 + c + 0·T` | NOT entailed | **negative control**: S1 must fall through, S3 must not discharge (range of `c` is `[1, 2^32)`, contains `1`) |

Consequence for the plan: no change to S1–S4. Two notes for O1: (i) the
0-coefficient pruning above; (ii) the two true P0 identities (masked count,
shift identity) are outside D1 (decide-only) by design and remain closer
work; they are the cases D1's "write rewrites back" alternative would buy.

### Timing

| date | phase | start | end | wall min | CPU min | notes |
|---|---|---|---|---|---|---|
| 2026-11-05 | O0 | — | — | 2.3 | 2.3 | ZZMmqShape.v dump (vm_compute+solve_vc 91 s, peak 7.7 GB); preamble checks < 1 s |
