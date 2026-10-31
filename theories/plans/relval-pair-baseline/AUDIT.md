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
