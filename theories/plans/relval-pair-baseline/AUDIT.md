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
