# relval-pair: soundness audit log (PLAN-relval-pair.md §5)

Sites where the tagged model made a NonSyncVal formula collapse to False/error
and the pair model needs a real decision instead. Under pairs, keeping the old
collapse would be UNSOUND in assumption position (it makes the branch vacuous),
and a green build does not catch it.

| Site | Old (tagged) | New (pair) |
|---|---|---|
| `Solver.v` `simplify_bool`, relval leaf | `SyncVal b => if b then empty else error`, NonSync => `error` | `if projL && projR then empty else error` |
| `Solver.v` `simplify_bool_neg`, relval leaf | NonSync => `error` | `if negb projL && negb projR then empty else error` |
| `Solver.v` `simplify_eq_val`, `term_relval` | NonSync => `error` | `if eq_dec rv (SyncVal v') then empty else error` |
| `Solver.v` `simplify_eq_relval`, `term_val`/`term_relval` | NonSync => `error` | `eq_dec` on the full pair |
| `Solver.v` `peval_formula_le'`, `unsigned` case | `0 <= unsigned t` rewritten to `secLeak t` (equivalent only because relop on NonSync was False) | `formula_true` (relops are pointwise, unsigned >= 0 on each side). Keeping the old rewrite would turn an ASSUMED bound into an ASSUMED publicness fact. |
| `Syntax/Formulas.v` `formula_bool`, `formula_relop` | NonSync => False | both projections |
| `Syntax/Formulas.v` `secLeak` | tag test | `projLeft = projRight` |
| `Symbolic/Worlds.v` `instprop_formula_eqs_nctx_sync` | conjunction of field `formula_eq`s <-> records equal AND `isSyncValRV` (true only because relop eq on NonSync was False) | records equal (pointwise); the "sync" conjunct is dropped -- field equalities say nothing about agreement |
| `Symbolic/Solver.v` `simplify_secLeak`, `term_binop`/`term_unop` | `secLeak (op t1 t2)` split into `secLeak t1 /\ secLeak t2`, spec'd as an EQUIVALENCE (exact only for the tag) | discharged to `true` when `secLeakT` proves it from the path condition, kept whole otherwise. The general simplifier runs on ASSUMPTIONS too, so splitting would assume publicness of the parts. Possibly coarser residuals for CFGVer solve_vc (watch in Phase 5). |
| `Symbolic/Solver.v` `instpred_formula_secLeak_{binop,unop}` | `⊣⊢` | `⊢` (parts public => result public); only that direction was ever used (`secLeakT_spec`) |
| `Symbolic/Solver.v` `formula_simplifies`, `bop.eq` case + `inst_relop_eq_split` | relop `t1 = t2` <-> `propeq t1 t2 /\ secLeak t1 /\ secLeak t2` | relop `t1 = t2` <-> `propeq t1 t2`. The old split, kept, would turn an ASSUMED equality into assumed publicness of both sides. As an obligation it is now strictly easier (no secLeak conjuncts). |
| `Symbolic/Solver.v` `try_bvadd_cancel` (relop eq/neq) | needed `secLeakT` on the shared summand (relop was False on NonSync) | still guarded (sound), but the guard is now unnecessary: cancellation holds per projection -- repair candidate |
| `Symbolic/Solver.v` `simplify_secLeak` (new wrapper, 411d1c89), bvec `c + s` / `s + c` with `c` a literal | (kept whole, see above) | rewritten to `simplify_secLeak_core s`. An EQUIVALENCE, so sound on assumptions and goals: `bv.add_cancel_l` per projection. Strips ONE layer (peval folds literals). Closes CountdownRec's `secLeak (0xc + q)` from `secLeak (0x8 + q)`. |

## Merge of KatamaranRel (PLAN-rsa / PLAN-arrv era), branch `issue/relval-rsa`, 2026-10-30

Assumption-side review of the solver/peval rules KatamaranRel added after the
branch point (d026cadc), plus the arrv model port. Same question as above:
does any rule, read as an ASSUMPTION, assume more than the pair model gives?

| Site | Old (tagged) | New (pair) |
|---|---|---|
| `Solver.v` `try_isolate_inner` (`x + s = y` ⟶ `x = y + (−1)·s`) | guard `secLeakT s` load-bearing: `NonSyncVal a a ≠ SyncVal a` | still guarded, now only a cost filter: per projection the inversion holds for ANY s (`relval_isolate` is a plain pointwise equivalence). Emitted as a `⊣⊢` rewrite either way, so sound on assumptions. Repair candidate: drop the guard. |
| `Solver.v` `ResimpSecLeak` (`resimp_secLeak_tri`, appended after a non-trivial unification) | `secLeak (ζ x)` re-split by the TAGGED `simplify_secLeak` (`secLeak (op a b) ⇔ secLeak a ∧ secLeak b` for every op) | unchanged code; sound because it emits `run (simplify_secLeak ..)` and `simplify_secLeak_spec` is `⊣⊢` here too. Weaker in effect: it splits only through the R3 ops below, otherwise re-emits `secLeak (ζ x)` whole. |
| `Solver.v` `simplify_secLeak_core`, R3 (`binop_secLeak_split`, `unop_secLeak_split`) | (every op split) | split ONLY for `cons`, `bvapp`, `rev` -- injective per projection, so `secLeak (op a b) ⇔ secLeak a ∧ secLeak b` exactly (`secLeak_binop_split`, `secLeak_unop_split`); sound on assumptions. NOT `append` (a public `v1 ++ v2` says nothing about v1/v2 without lengths) and NOT `regroup` (its eval is junk `[]` off `(bvec m, bvec 8)`). |
| `Solver.v` `simplify_secLeak_core`, R3 ORDER (2026-10-31) | (no guard) | the R3 split is tried BEFORE the `secLeakT` discharge. With the guard first, ResimpSecLeak got `formula_true`: right after `vs := x :: r` the substituted path condition holds the exact term `secLeak (x :: r)`, so `secLeakT` said "known" and the parts were never emitted (RsaSpikeSb `valid_cpy` residual `secLeak r.1`, solver call checked directly). Exact for these ops, so no soundness change; a goal `secLeak (x :: r)` now needs the parts, which ResimpSecLeak supplies in the one case the whole term reaches the path condition (substitution). |
| `PartialEvaluation.v` new rules (`peval_sext`, `bvtake_zext`, `append`, `rev`, `regroup`) | proved by a two-case destruct | pure-term rewrites (`≡` on `inst`), sound on any RelVal by the homomorphic lift (relval-rewrite-over-secrets); only the proof scripts changed (one case). |
| `IrisInstanceBinary.v` `interp_arrv` | `match a, n, e with SyncVal.. => body | _ => False` | `⌜secLeak a ∧ secLeak n ∧ secLeak e⌝ ∗ interp_arrv_body (projL a) (projL n) (projL e) vs`, as `interp_arr` above; bridges `interp_arrv_SV`, `interp_arrv_agree`. The body already read only projections of `vs`. |

## R1 + R4 (PLAN-relval-pair §12.0 D-M5), branch `issue/relval-rsa`, 2026-10-31

All four are `≡` rewrites (peval) or a one-way discharge (secLeakT), so on the
assumption side they assume nothing the pair model does not give.

| Site | Old (tagged) | New (pair) |
|---|---|---|
| `PartialEvaluation.v` `canon_with` (ring normal form) | sound per projection (`teq side`) plus a LEAF CERTIFICATE; a cancelled atom padded back as `0 * a` (the tag of `x - x` for a secret x was NonSync, so dropping it was unsound) | upstream's `norm_aux`/`Pphi_dev` modulo `≡` from `Term_bv_ring_theory` (restored in `Instantiation.v`; `TermRing` has its ring fields again). A cancelled atom is dropped: `x - x ⇝ 0` is exact on pairs. Atom sort and `clean` kept. |
| `PartialEvaluation.v` `peval_bvand_id`, `peval_bvxor_id` (off the mask path, not both literals) | (none: `0 & m` for a secret m was NonSync 0 0, not `SyncVal 0`) | `0 & t`, `t & 0` ⇝ 0; `t ^ t` ⇝ 0; `0 ^ t`, `t ^ 0` ⇝ t. Per projection, `≡`. |
| `Solver.v` `drop_pub_zero` | dropped `0 * a` only for a PUBLIC a (secLeakT) | deleted: peval no longer produces `0 * a`. |
| `Solver.v` `secLeakT` base case (`secLeak_base`) | exact `secLeak t` in wco | also: `t = u` (either order) in wco with `secLeakT_noeq u` (ONE hop). Only ever used to DISCHARGE (`secLeakT_spec` is `⊢`), and in `simplify_secLeak_core` on an assumption it drops a formula already implied by wco. |

## propeq decomposition (RSA cleanup), branch `issue/relval-rsa`, 2026-10-31

A bi-implication (`simplify_propeq_spec` is `⊣⊢`), so it is exact both as an
assumption and as an obligation.

| Site | Old (tagged) | New (pair) |
|---|---|---|
| `Solver.v` `simplify_propeq_binop` (the `term_binop` arm of `simplify_propeq`) | every binop opaque: `h :: hs = x :: xs` stayed ONE equation, so unification never substituted `x` (RsaCcopy's `take_any` heads) | `pair`/`cons`/`bvapp`/`bvcons` decompose argument-wise, reusing `simplify_eq_binop_{pair,cons,bvapp,bvcons}`; exact since `c a b = c a' b'` iff both projections agree iff `a = a'` and `b = b'` (`propeq_{pair,cons,bvapp,bvcons}_split`, via `ty.RV_ext`). Every other operator: unchanged. |

## Tag-workaround removal (D-M4 part 1), branch `issue/relval-rsa`, 2026-11-01

| Site | Old (tagged) | New (pair) |
|---|---|---|
| `PartialEvaluation.v` `peval_append` fall-through (`peval_append_nil`) | (none) | `t ++ [] ⇝ t`; per projection `l ++ [] = l`, so `≡` (`peval_append_nil_sound`). |
| `Solver.v` `simplify_propeq_unop_rev` (the `uop.rev` arm of `simplify_propeq`) | `rev` opaque | `rev a = rev b` ⇝ `a = b`, `rev a = v` ⇝ `a = rev v`: rev is injective per projection, so `⊣⊢` (`propeq_rev_split`, `propeq_rev_val`). Needed by memmove, whose flipped arrays give `rev vs = []`. |
| `Verifier.v` / `SpecIris.v` `clem_arrv_empty_elim` | `arrv a 0 e vs ⊢ a = e`, never `vs = []` (`NonSyncVal [] []` is not `SyncVal []`) | for w ≥ 1 also `vs = []`: `interp_arrv_count0` gives `[]` on both projections, and that pair IS `[]`. w = 0 unchanged (cells own no bytes). |
| `Verifier.v` / `SpecIris.v` `clem_arrv_count0` (new) | (n/a) | the same `vs = []`, w ≥ 1, keeping the array; precondition False at w = 0. Replaces `pad`. |
| deleted CLems | `take_cons` (pattern take), `take_any` (angelic take_cons/take_first), `resync_head` + `clem_mux_byte` (MUX of two equal bytes back to the byte), `pad` (absorb an empty remainder's value) | each existed only because of the tag: cons was not injective in equations, MUX(secret,u,u) was not u, and a length-0 value was not []. Their soundness lemmas (and the helpers `interp_arrv_take_cons`, `interp_arrv_pad`, `mux_byte_same`) are gone with them; nothing is assumed in their place. |
