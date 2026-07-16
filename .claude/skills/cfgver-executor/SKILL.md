---
name: cfgver-executor
description: >
  Katamaran CFGVer symbolic executor & verification condition — the decision layer.
  Use when reading or writing the symbolic side of the CFG verifier: sexec_cfg_addr
  (symbolic executor over a gmap of instructions keyed by absolute pc), the angelic
  exit/execute choice at each step, why execution errors on a symbolic pc
  (term_get_val = None) or an unmapped address, ptsto_instrs / ptsto_instrs_lookup
  (instruction-memory ownership), and sblock_verification_condition (how the VC is
  built and called). NOT for the concrete mirror executor cexec_cfg_addr or
  rsolve/relational proofs (cfgver-refinement), and NOT for the VC-to-leakage chain
  (cfgver-soundness).
---

# CFGVer symbolic executor & VC

The decision layer of the verifier: what the symbolic executor computes and how the
VC is assembled from it. The concrete mirror (`cexec_cfg_addr`) and the proofs
relating the two live in **cfgver-refinement**.

## Instruction store

Instructions live in a **`gmap (bv xlenbits) AST` keyed by absolute pc**. The map is
built at the `Examples.v` boundary by `instrs_of_list (bv.of_N init_addr) i` from a
plain `list AST`; `Verifier.v` itself knows nothing about a base address, alignment,
or index arithmetic — lookup is exact: `instrs !! v`.

## `sexec_cfg_addr`

```coq
sexec_cfg_addr (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
  : ⊢ STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits)
```

At each step it takes an `angelic_binary` (existential choice) between **exiting**
and **executing** the instruction at the current pc
(`angelic_binary m1 m2 Φ h = m1 Φ h \/ m2 Φ h`).

It stops with `error` when:
- `fuel = 0`
- `term_get_val apc = None` — the pc is symbolic, not a concrete value
- `instrs !! v = None` — no instruction mapped at this pc

## `ptsto_instrs`

```coq
Definition ptsto_instrs (instrs : gmap (bv xlenbits) AST) : iProp Σ :=
  ([∗ map] a ↦ i ∈ instrs, interp_ptsto_instr (SyncVal a) (SyncVal i))%I.
```

Access one instruction with `ptsto_instrs_lookup instrs v Hlk`
(`Hlk : instrs !! v = Some i`, via `big_sepM_lookup_acc`; `i` is implicit).

## `sblock_verification_condition`

```coq
sblock_verification_condition {Σ : LCtx}
  (req : Assertion (Σ ▻ "a"∷ty_xlenbits))
  (instrs : gmap (bv xlenbits) AST)
  (exitCond : bv xlenbits -> bool)
  (fuel : nat)
  (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
  (w : World) : 𝕊 w
```

Call pattern: `sblock_verification_condition (Σ := [ctx]) req instrs exitCond fuel ens wnil`.
`Σ := [ctx]` must be explicit — Coq cannot infer it.

**Postconditions are trivial by design**: `SHeapSpec` has no leakcheck — resources
left in the heap after consuming `ens` are silently dropped (affinely, in Iris).
`CFGVerifierContract` therefore exposes no postcondition field; `CFG_VC_triple` uses
the trivially-true assertion as `ens`, and the soundness lemmas discard the final heap.

## Dead code & history

`semTripleCFG` and `instrAligned` still exist in `Verifier.v` but nothing uses them
(pending cleanup). Before 2026-07-13 instructions were a `list AST` with a base
address and alignment guard; see git history or memory `project-cfgver-gmap-pivot`
if archaeology is needed.

> **⚠ Known gap — parametric-base table executor not yet covered by any skill.**
> The symbolic-base work added a second executor path (`sexec_cfg_addr_tbl`, dispatch
> by `Term_eqb ∘ peval` on term-table keys so a symbolic pc like `p+8` works) plus
> `sblock_verification_condition_tbl` and `gen_contract_rel`. Until a skill covers it,
> consult the "PARAMETRIC-BASE SUPPORT — READING GUIDE" comment blocks in
> `CFGVer/Verifier.v` / `CFGVer/Examples.v` and memory `project-cfgver-symbolic-base-poc`.

**Next layer up:** the concrete mirror and the relational proofs are in
**cfgver-refinement**; the VC→`myWP2_loop`→leakage bridge is in **cfgver-soundness**.
