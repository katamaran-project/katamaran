---
name: cfgver-executor
description: >
  Katamaran CFGVer symbolic executor & verification condition — the decision layer.
  Use when reading or writing the symbolic side of the CFG verifier: sexec_cfg_addr
  (symbolic executor over a term-keyed instruction table), the angelic exit/execute
  choice at each step, why execution errors on a pc that matches no table key
  (lookup_instr/is_exit fail), ptsto_instrs / ptsto_instrs_lookup (instruction-memory
  ownership, still gmap-based on the concrete side), and scfg_verification_condition
  (how the VC is built and called). NOT for the concrete mirror executor cexec_cfg_addr or
  rsolve/relational proofs (cfgver-refinement), and NOT for the VC-to-leakage chain
  (cfgver-soundness).
---

# CFGVer symbolic executor & VC

The decision layer of the verifier: what the symbolic executor computes and how the
VC is assembled from it. The concrete mirror (`cexec_cfg_addr`) and the proofs
relating the two live in **cfgver-refinement**.

## Instruction store

Two representations, one per side. The **concrete** executor (`cexec_cfg_addr`,
**cfgver-refinement**) still keys off a **`gmap (bv xlenbits) AST` by absolute pc**,
built by `instrs_of_list (bv.of_N init_addr) i` (`Tables.v`) from a plain `list AST` —
lookup is exact, `instrs !! v`. The **symbolic** executor (`sexec_cfg_addr`, below)
instead keys off a **term-indexed table** (`SInstrTable`/`SExitTable`, a `list (Term _
ty_xlenbits * AST)` resp. `list (Term _ ty_xlenbits)`) so that a symbolic pc like
`p + 8` can still be dispatched: matching is syntactic (`Term_eqb` modulo `peval`),
not a concrete lookup. `itable_faith`/`etable_faith` (`Verifier.v`) are the Prop-level
facts tying a given table to the gmap at a valuation; the refinement proof
(`rexec_cfg_addr`, **cfgver-refinement**) is what lets the two sides' VCs
correspond.

## `sexec_cfg_addr`

```coq
sexec_cfg_addr (fuel : nat)
  : ⊢ SInstrTable -> SExitTable -> STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits)
```

At each step it takes an `angelic_binary` (existential choice) between **exiting**
and **executing** the instruction at the current pc
(`angelic_binary m1 m2 Φ h = m1 Φ h \/ m2 Φ h`). Unlike a gmap lookup, `apc` never
needs to be concrete: `lookup_instr`/`is_exit` match it against the table's key terms
via `Term_eqb (peval apc) (peval key)`, so a literal base (`256+8` folds to `264`) and
a symbolic one (`p+8` matches the key term `p+8`) both work. `tbl`/`exits` are
threaded as recursion ARGUMENTS (not fixed `Fixpoint` params, since they're
world-dependent) and persisted across each step via `persist_itable`/`persist_etable`.

It stops with `error` when:
- `fuel = 0`
- `lookup_instr tbl apc = None` — the pc matches no table key (no instruction there)
- `is_exit exits apc = false` on the exit branch (chosen but no exit key matches)

## `ptsto_instrs`

```coq
Definition ptsto_instrs (instrs : gmap (bv xlenbits) AST) : iProp Σ :=
  ([∗ map] a ↦ i ∈ instrs, interp_ptsto_instr (SyncVal a) (SyncVal i))%I.
```

Access one instruction with `ptsto_instrs_lookup instrs v Hlk`
(`Hlk : instrs !! v = Some i`, via `big_sepM_lookup_acc`; `i` is implicit).

## `scfg_verification_condition`

```coq
scfg_verification_condition {Σ : LCtx}
  (req : Assertion (Σ ▻ "a"∷ty_xlenbits))
  (tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits))
  (fuel : nat)
  (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
  (w : World) : 𝕊 w
```

Call pattern: `scfg_verification_condition (Σ := [ctx]) req tbl exits fuel ens wnil`.
`Σ := [ctx]` must be explicit — Coq cannot infer it. `tbl`/`exits` are given at the
CONTRACT context Σ (like `req`/`ens`) and substituted into the current world via
`subst_itable`/`subst_etable`. This is the VC every `CFGVerifierContract` actually
builds (`Contracts.v`'s `CFG_VC_triple`) — including fixed-address examples, whose
table entries are just literal-term keys.

**Postconditions are trivial by design**: `SHeapSpec` has no leakcheck — resources
left in the heap after consuming `ens` are silently dropped (affinely, in Iris).
`CFGVerifierContract` therefore exposes no postcondition field; `CFG_VC_triple` uses
the trivially-true assertion as `ens`, and the soundness lemmas discard the final heap.

For the parametric-base story specifically (why a *term*-keyed table rather than a
gmap in the first place), consult the "PARAMETRIC-BASE SUPPORT — READING GUIDE"
comment blocks in `CFGVer/Verifier.v` / `CFGVer/GenContract.v` and memory
`project-cfgver-symbolic-base-poc`.

**Next layer up:** the concrete mirror and the relational proofs are in
**cfgver-refinement**; the VC→`myWP2_loop`→leakage bridge is in **cfgver-soundness**.
