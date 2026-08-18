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
iApply (cfg_instrs_safe γ1 γ2 contract).
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
iApply (cfg_instrs_safe_with_mem γ1 γ2 data_specs μ1 μ2 contract).
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
(explicit: `γ1, γ2, data_specs, μ1, μ2, contract`). Passing `data_specs` where a
`RegStore` is expected is the tell.

The same applies to the `gen_contract_noninterferent_rel*` **bridges**, and it
bites when one bridge delegates to another (as `_param` does to `_rel_classed`
since 2026-08-18). **Every** data argument — `reg_specs`, `mem_specs`, `instrs`,
`extra_exit_offs`, `bound`, `exitCond`, `fuel`, `init_addr` — is implicit, because
each occurs in some premise's type, so the first *explicit* argument is `HND`. The
tell is a type error naming `NoDup`:

```
The term "map reg_spec_to_rel reg_specs" has type "list reg_spec_rel"
while it is expected to have type "NoDup (map reg_spec_idx (map (concretize_reg ?init_addr) ?reg_specs))"
```

Use the `(name := v)` form (implicits accept it; explicit arguments do not).
**Which ones you must name:** anything the *conclusion* does not mention.
`noninterferent_strong` mentions only `init_addr`, `instrs`, `exitCond` and the two
spec lists, so `bound`, `fuel` and `extra_exit_offs` all float — and so does
`mem_specs` when you are instantiating it at `[]`, for a reason worth knowing:

> **Unification will not solve `map f ?l ≡ []`.** Verified in 9 ms on a scratch
> probe — `eapply` on a `map S ?l = map S ?l` lemma against `[] = []` fails with
> *"Unable to unify `map S ?M = map S ?M` with `[] = []`"*. The conclusion's data
> slot is `map (concretize_mem init_addr) ?mem_specs`, so a bare `eapply` can never
> pin `?mem_specs := []`. Supplying it by **name** succeeds instead, because that
> route goes through *conversion* (`map f [] ≡ []` definitionally) rather than
> unification.

Pin all four by name and nothing floats, which also means the "discharge
`valid_contract` FIRST" ordering hazard cannot arise and premises may be
discharged in order. Conversely, the goal-determined arguments (`reg_specs` here)
should be left to unification — but only after the goal has been rewritten into
the concretized form, since `map (concretize_reg ia) (map reg_spec_to_rel rs) = rs`
(`map_concretize_reg_to_rel`) is **not** definitional for a variable list.

## The unified bridge (`gen_contract_noninterferent_u`)

Since 2026-08-18 there are only **two** real bridge implementations —
`gen_contract_noninterferent_u` (general) and `_u_simple` — over
`gen_contract_u`'s two data lists. `_param`, `_param_simple`,
`_rel_classed_simple` and `_rel_bytes_simple` survive as *thin delegations*, which
is deliberate: calling `_u` directly costs a goal rewrite, two mandatory named
implicits, an ordering line and two extra bullets **at every call site**, so the
wrappers exist to absorb that instead of exporting it to 13 `Result` files. The
three general bridges (`_rel`, `_rel_classed`, `_rel_bytes`) were deleted.

`_u` concludes over the CONCATENATION `word_data ++ byte_data`, matching the
concatenation the trusted side already assumed. Its `ImplPre` therefore splits
both the resource and the hypotheses, via three small lemmas added for it:
`interp_mem_app` (just `map_app` + `big_sepL_app`, since
`interp_mem_with_public_memory` is a `big_sepL`), `gen_init_mem_app`, and
`declare_init_mem_app`. This is the generalisation the old `_bytes` bridge's
header comment explicitly asked for, having fixed its word list to `[]` to avoid
exactly this split.

Three traps when delegating to it, each of which is a *different* answer for the
two granularities:

- **`[] ++ B` reduces definitionally; `A ++ []` does not** (for a variable `A`).
  So the byte-only case needs no goal rewrite, while the word-only case must open
  with `rewrite <- (app_nil_r mem_specs)` and then `rewrite app_nil_r` in the
  `HDataAddrs` and `Hlen` premises.
- **`word_data`/`byte_data` must still be named even when `[]`**, for the
  `map f ?l ≡ []` reason above.
- **`gen_init_mem_app` is `omap_app` — do not hand-roll the induction.** `cbn`
  rewrites `omap` to `list_omap` while the IH keeps it folded, so `rewrite IH`
  fails with "found no subterm". stdpp already has `omap_app`; `unfold
  gen_init_mem. apply omap_app.` is the whole proof.

Ordering constraint worth knowing before moving anything: `_u` depends on
`gen_implpre_mem_bytes`, so **nothing above that lemma can reference `_u`** —
which is why the thin delegations live at the END of `EndToEnd.v`, below the
unified pair, rather than where their predecessors sat.

## What the wiring proofs carry and materialize

The chain threads the gmap instruction ownership
`ptsto_instrs (instrs_of_list (bv.of_N init_addr) instrs')`, materialized from raw
memory by `instrsMemory` (code only) / `instrsAndDataMemory` (code + data words) /
`intro_ptsto_instrs` — internally via `big_sepM_insert` with side condition
`instrs_of_list_fresh`.

## The CLASSED memory `ImplPre` (`gen_implpre_mem_class`)

For a contract built with `gen_contract_rel_classed` (→ **cfgver-gen-contract**),
the data block's `ImplPre` cannot reuse the `gen_mem_pre_rel_concretize` +
`gen_implpre_mem` pair, because no concrete classed builder exists to rewrite
into (the width-index trap, `GenContract.v:536`). `gen_implpre_mem_class` attacks
the rel assertion directly, in four moves:

| step | lemma |
|---|---|
| split the resource list three ways | `interp_mem_partition_rel` (→ `interp_mem_partition` + the `filter_*_concretize` commutations) |
| pinned group | `gen_mem_pre_rel_concretize` + `gen_implpre_mem` — the concretize rewrite IS available for that group |
| public class | `interp_mem_group_pub` + `gen_mem_pub_class_ks_intro` |
| private class | `interp_mem_group_priv` + `gen_mem_priv_class_ks_intro` |

`interp_mem_partition_rel` is provable at all only because Iris's
`big_opL_permutation` applies to index-INDEPENDENT bodies (`λ _ : nat, f`), and
`interp_mem_with_public_memory`'s body ignores the index.

Four traps, each of which cost a round trip:

- **The per-group lemmas need only the `is_pub` hypothesis, not `is_exist`.**
  `interp_mem_with_public_memory` branches on the publicness bit and ignores the
  value slot entirely, so the group conversion never has to know the group is
  `PVExist`.
- **`μ1`/`μ2` are IMPLICIT in `gen_implpre_mem_class`** (they occur in
  `HInitMem1`'s type, under `Set Implicit Arguments`) — and this differs from the
  same statement at a file's top level. Passing them positionally reports
  `"μ1 has type Memory while RelVal ty_xlenbits was expected"`, which reads like a
  statement bug. Passing the whole call by name instead fails too: Coq's
  `(x := v)` accepts implicit names only (`Wrong argument name HInitMem2 (possible
  names: Σ H μ1 μ2)`). The working form is positional and μ-free.
- **`gen_init_mem_filter_pinned`** is why the caller's *unfiltered*
  `declare_init_memory` hypotheses suffice for the pinned group. Its proof needs
  `unfold gen_init_mem in *` — unfolding in the goal only leaves the IH folded and
  `rewrite IH` finds no subterm.
- In this file's notation environment `rewrite A, B` (comma form) is a **syntax
  error**, and so is a one-element delta flag `cbn [map]` (while
  `cbn [map List.filter]` parses) — write two `rewrite`s and `cbn [List.map]`.

## Register-machinery reference

The two-world register ownership predicates these proofs manipulate
(`declare_public_registers`, `interp_gprs_with_(public_)registers`,
`something_registers`, `declare_pub_*`) are documented in
`.claude/skills/cfgver/references/registers.md`.
