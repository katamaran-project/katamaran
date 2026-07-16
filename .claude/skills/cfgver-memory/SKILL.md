---
name: cfgver-memory
description: >
  Katamaran CFGVer public-memory infrastructure and data-memory end-to-end. Use when a
  verified program reads or writes DATA MEMORY: cfg_instrs_endToEnd_with_memory,
  cfg_instrs_verified_with_mem / cfg_instrs_safe_with_mem, and the public-memory
  ownership predicates — mem_spec, declare_public_memory, gen_public_addrs,
  interp_mem_with_memory / interp_mem_with_public_memory, the something_memory
  equivalence, and instrsAndDataMemory (splitting raw memory into ptsto_instrs +
  data words). Extends the register-only cfgver-endtoend skill. NOT for the
  memory-word preconditions written INSIDE the contract itself (gen_mem_pre /
  mem_full_spec — use cfgver-contracts).
---

# CFGVer public-memory infrastructure

Data-memory extension of the end-to-end wiring. This is the register-machinery
(→ **cfgver-contracts** / **cfgver-endtoend**) mirrored for programs that also access
data memory. Read **cfgver-endtoend** first for the register-only base lemma.

`instrsAndDataMemory` and `intro_ptsto_instrs` yield the gmap
`Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs (instrs_of_list (bv.of_N start)
instrs)` (via `big_sepM_insert`, side condition `instrs_of_list_fresh`).

## Types and definitions (all in `CFGVer/Examples.v`)

```coq
(* mem_spec: (word-address, is_public) *)
Definition mem_spec : Type := Val ty_word * bool.

(* Prop: μ1 and μ2 agree on every address in the public subset of specs *)
Definition declare_public_memory (μ1 μ2 : Memory) (addrs : list (Val ty_word)) : Prop :=
  Forall (fun a => get_word μ1 a = get_word μ2 a) addrs.

(* The public addresses from a spec list *)
Definition gen_public_addrs (specs : list mem_spec) : list (Val ty_word) :=
  base.omap (fun '(a, pub) => if pub then Some a else None) specs.

(* Two-world memory ownership — all entries as NonSyncVal (raw form) *)
Definition interp_mem_with_memory `{sailGS2 Σ} (μ1 μ2 : Memory)
    (specs : list mem_spec) : iProp Σ :=
  [∗ list] spec ∈ specs,
    let '(a, _) := spec in
    interp_ptstomem (width := 4) (SyncVal a)
      (NonSyncVal (get_word μ1 a) (get_word μ2 a)).

(* Two-world memory ownership — public entries as SyncVal, private as NonSyncVal *)
Definition interp_mem_with_public_memory `{sailGS2 Σ} (μ1 μ2 : Memory)
    (specs : list mem_spec) : iProp Σ :=
  [∗ list] spec ∈ specs,
    let '(a, pub) := (spec : mem_spec) in
    if pub
    then interp_ptstomem (width := 4) (SyncVal a) (SyncVal (get_word μ1 a))
    else interp_ptstomem (width := 4) (SyncVal a)
           (NonSyncVal (get_word μ1 a) (get_word μ2 a)).
```

## `something_memory` equivalence

```coq
Lemma something_memory `{sailGS2 Σ} μ1 μ2 (specs : list mem_spec)
    (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs specs)) :
  interp_mem_with_memory μ1 μ2 specs ⊣⊢
  interp_mem_with_public_memory μ1 μ2 specs.
```

Usage: `rewrite (something_memory data_specs HpubMem)` rewrites `interp_mem_with_memory`
to `interp_mem_with_public_memory` in the current Iris proof state (including hypothesis
types, since Iris environments are Coq terms).

## `instrsAndDataMemory`

Extracts `ptsto_instrs ∗ interp_mem_with_memory` from the raw `mem_res2_without_leak`.
Data words must occupy the `4*|data_specs|` bytes immediately following the instruction
region.

```coq
Lemma instrsAndDataMemory `{sailGS2 Σ} {μ1 μ2} ws_instrs data_specs instrs :
  (4 * N.of_nat (length instrs) + 4 * N.of_nat (length data_specs) < lenAddr)%N →
  mem_has_instrs μ1 (bv.of_N init_addr) ws_instrs instrs →
  mem_has_instrs μ2 (bv.of_N init_addr) ws_instrs instrs →
  (∀ i spec, data_specs !! i = Some spec →
    spec.1 = bv.of_N (init_addr + 4 * N.of_nat (length instrs) + 4 * N.of_nat i)) →
  mem_res2_without_leak μ1 μ2 ⊢ |={⊤}=>
    ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs ∗
    interp_mem_with_memory μ1 μ2 data_specs.
```

## `cfg_instrs_verified_with_mem` / `cfg_instrs_safe_with_mem`

Memory-aware variants of `cfg_instrs_verified` / `cfg_instrs_safe`. The `ImplPre`
parameter also receives `interp_mem_with_public_memory μ1 μ2 data_specs` — they
exist because `ImplPre`'s Iris spatial context starts empty, so memory ownership
must be threaded through as a conjunct rather than framed from outside.

Their call patterns, implicit-argument asymmetry, and proof-body idioms are in the
**cfgver-endtoend-internals** skill (needed only when modifying the wiring lemmas).

## `cfg_instrs_endToEnd_with_memory`

Extension of `cfg_instrs_endToEnd` (→ **cfgver-endtoend** skill) for programs with data
memory. Requires:
- `data_specs : list mem_spec`
- `HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs data_specs)`
- `HDataAddrs` mapping spec indices to concrete addresses (contiguous after instruction region)
- `ImplPre` now also takes `interp_mem_with_public_memory μ1 μ2 data_specs`

The length bound is `4 * |instrs| + 4 * |data_specs| < lenAddr` (combined).
`instrsAndDataMemory` is proved.
