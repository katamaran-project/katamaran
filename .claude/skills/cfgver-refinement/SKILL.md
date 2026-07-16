---
name: cfgver-refinement
description: >
  Katamaran CFGVer refinement layer — the concrete (shallow) executor cexec_cfg_addr
  that mirrors the symbolic sexec_cfg_addr, the RefineCompat relation structure, and
  the rexec_cfg_addr relational-correctness lemma. Use when reading or extending the
  relational layer, proving a new relational (ℛ⟦⟧) lemma, or understanding why the
  concrete mirror exists at all. NOT for driving or debugging the rsolve tactic
  itself — failures, hangs, memory blowups, missing instances — that is
  cfgver-rsolve. NOT for the symbolic executor's own semantics (cfgver-executor).
---

# CFGVer refinement: the concrete mirror + relational correctness

Proof apparatus, not decision logic. `cexec_cfg_addr` is the concrete (shallow,
`CHeapSpec`) executor mirroring `sexec_cfg_addr` step for step; it exists so the
soundness argument can factor as

```
symbolic VC  --(refinement: rexec, this skill)---------->  concrete execution
             --(Iris soundness: cfgver-soundness)-------->  myWP2_loop / leakage
```

## What cexec mirrors from sexec — and what it doesn't

Side by side (`Verifier.v:234` vs `:491`), the executors share their entire
monadic skeleton:

| Decision point | `sexec_cfg_addr` (symbolic) | `cexec_cfg_addr` (concrete) |
|---|---|---|
| fuel | `match fuel` → `error` / step | identical |
| pc probe | `term_get_val apc` — *is the term a literal?* | `ty.RVToOption apc` — *do both worlds agree (SyncVal)?* |
| choice | `angelic_binary` exit / execute | identical |
| exit branch | `if exitCond v then pure apc else error` | identical |
| dispatch | `instrs !! v` → `error` / instruction | identical |
| step | `⟨θ1⟩ apc' <- sexec_instruction i apc ;; recurse` | `apc' <- cexec_instruction i apc ;; recurse` |

**MIRROR (mandatory):** every bind, case split, and angelic choice, in the same
order. `rexec_cfg_addr` and `rsolve` pair the two programs *structurally* — one
`refine_bind` per bind, one instance per choice point. A skewed skeleton (fused
binds, reordered branches, an extra case on one side) makes instance search
diverge — the `memory_exhausted` failure in **cfgver-rsolve**.

**TRANSLATE (same shape, shifted meaning):** the pc probe. Symbolic
"term is a concrete literal" becomes concrete "the two-world `RelVal` is a
`SyncVal`". Keep the decision point; translate its predicate.

**DON'T MIRROR (symbolic-only bookkeeping):** world-indexed binds (`⟨θ1⟩`
substitutions), path conditions, and error-message payloads (`amsg` with
`debug_string_pathcondition`; concrete errors are a bare `error`). These have no
concrete counterpart and adding analogues would only break the pairing.

Above the executors sit `cexec_triple_addr` (demonic Σ/pc intro → `produce req` →
run → `consume ens`) and `cblock_verification_condition = CHeapSpec.run …` — note
the source comment: `run` performs **no leakcheck**.

## `RefineCompat` — the relation structure

Relational goals between symbolic and concrete programs are closed instance-by-
instance via the typeclass

```coq
Class RefineCompat (R : 𝕊 w -> C -> Prop) (c : C) (w : World) (s : 𝕊 w) ... :=
  MkRefineCompat { refine_compat : R s c }.
```

Key instances in `CFGVer/Verifier.v`: `refine_compat_angelic_binary` and
`refine_compat_block_verification_condition` (the full VC). The tactic that drives
the instance search is `rsolve` — using and debugging it effectively is the
**cfgver-rsolve** skill.

## `rexec_cfg_addr`

The relational-correctness lemma for `sexec_cfg_addr` vs `cexec_cfg_addr`, proved by
`iInduction` on fuel: at each step the angelic exit/execute choice on both sides is
paired, then the per-instruction executions are related, then the induction
hypothesis closes the loop.

In its execute branch, `destruct (instrs !! v)` silently fails to reduce the `match`
and `refine_bind` then diverges — that is a generic stdpp-gmap pitfall; see the
**gmap-pitfalls** skill for the mechanism and fix.
