---
name: cfgver-endtoend-internals
description: >
  Internal proof structure of Katamaran CFGVer's wiring lemmas — library skill,
  normally reached from cfgver-endtoend or cfgver-memory. Consult when MODIFYING or
  extending cfg_instrs_endToEnd / cfg_instrs_endToEnd_with_memory themselves, or the
  cfg_instrs_verified(_with_mem) / cfg_instrs_safe(_with_mem) lemmas they build on:
  the iApply cfg_instrs_safe proof-body pattern, the double-iFrame idiom, the
  _with_mem call pattern with its implicit-argument asymmetry, and why the _with_mem
  variants exist (empty spatial context in ImplPre). For USING the wiring see
  cfgver-endtoend.
---

# End-to-end wiring lemmas: proof internals

How `cfg_instrs_endToEnd(_with_memory)` are proved inside — needed when extending
them (as was done for the memory variant), not when calling them.

## Register-path proof body (`cfg_instrs_endToEnd`)

```coq
iApply (cfg_instrs_safe γ1 γ2 block).
all: eauto.
iIntros "(Hregs & Hpriv & #Hinv')".
iApply ImplPre.          (* NOT iApply (ImplPre Σ') — Σ is implicit, inferred *)
iFrame "∗ #".
by iFrame "∗ #".         (* second iFrame closes the residual after the first *)
```

- `iApply (ImplPre Σ')` fails with "expected gFunctors": `Σ` is explicit in
  `forall`-with-typeclass position; apply with no argument and let the ambient
  Iris context infer it.
- The **double `iFrame`** is load-bearing: the first frames the register/privilege
  resources, the second closes the residual `interp_gprs` goal. Omitting the second
  surfaces as a "Wrong bullet" error later.

## Memory-path proof body (`cfg_instrs_endToEnd_with_memory`)

```coq
iApply (cfg_instrs_safe_with_mem γ1 γ2 data_specs μ1 μ2 block).
all: eauto.
iIntros "(Hregs & Hmem & Hpriv & #Hinv')".
iApply ImplPre.
rewrite <- (something_registers HpubReg).
iFrame "Hmem ∗ #".
by iFrame "∗ #".
```

- `rewrite <- (something_registers HpubReg)`: the goal at that point already has
  `interp_gprs_with_public_registers`, so the rewrite goes right-to-left (the lemma's
  LHS is the non-public form).

## Why the `_with_mem` variants exist

`cfg_instrs_safe`'s `ImplPre` starts with an **empty Iris spatial context** — outer
hypotheses are invisible inside it, so memory ownership held outside cannot be
framed in (`iFrame "Hmemdata …"` fails with "not found"). `cfg_instrs_safe_with_mem`
threads `interp_mem_with_public_memory μ1 μ2 data_specs` through as a conjunct in
`ImplPre`'s domain instead.

## Implicit-argument asymmetry

`Set Implicit Arguments` makes `data_specs, μ1, μ2` implicit in
`cfg_instrs_verified_with_mem` (they appear in `ImplPre`'s type; first explicit
argument is `γ1 : RegStore`) but **explicit** in `cfg_instrs_safe_with_mem`
(explicit: `γ1, γ2, data_specs, μ1, μ2, block`). Passing `data_specs` where a
`RegStore` is expected is the tell.

## Register-machinery reference

The two-world register ownership predicates these proofs manipulate
(`declare_public_registers`, `interp_gprs_with_(public_)registers`,
`something_registers`, `declare_pub_*`) are documented in
`.claude/skills/cfgver/references/registers.md`.
