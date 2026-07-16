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
