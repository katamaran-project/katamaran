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
  mem_full_spec — use cfgver-gen-contract).
---

# CFGVer public-memory infrastructure

Data-memory extension of the end-to-end wiring. This is the register-machinery
(→ **cfgver-gen-contract** / **cfgver-endtoend**) mirrored for programs that also access
data memory. Read **cfgver-endtoend** first for the register-only base lemma.

`instrsAndDataMemory` / `intro_ptsto_instrs` produce the instruction-memory
ownership (`ptsto_instrs`) plus the data-word ownership for you (their proof
mechanics: → **cfgver-endtoend-internals**).

## Types and definitions (statement-level in `Noninterference.v`; Iris-level in `Adequacy.v`/`EndToEnd.v`)

```coq
(* Noninterference.v (since PLAN-spec-layer, 2026-10-09): one word of a
   mem_layout's cells; the statement passes `cells mem`. *)
Definition mem_cell : Type := N * val_spec (Val ty_word).

(* Prop: μ1 and μ2 agree on every address in the public subset of specs *)
Definition declare_public_memory (μ1 μ2 : Memory) (addrs : list (Val ty_word)) : Prop :=
  Forall (fun a => get_word μ1 a = get_word μ2 a) addrs.

(* The Public cells' addresses *)
Definition gen_public_addrs (cs : list mem_cell) : list (Val ty_word) :=
  base.omap (fun '(a, s) => match s with Public => Some (bv.of_N a) | _ => None end) cs.

(* Adequacy.v: a cell's address as a word, and whether it is Public.  Known and
   Secret cells take the per-run (NonSyncVal) route. *)
Definition cell_addr (s : mem_cell) : bv word := bv.of_N s.1.
Definition cell_pub (s : mem_cell) : bool := match s.2 with Public => true | _ => false end.

(* Two-world memory ownership — all entries as NonSyncVal (raw form) *)
Definition interp_mem_with_memory `{sailGS2 Σ} (μ1 μ2 : Memory)
    (specs : list mem_cell) : iProp Σ :=
  [∗ list] spec ∈ specs,
    let a := cell_addr spec in
    interp_ptstomem (width := 4) (SyncVal a)
      (NonSyncVal (get_word μ1 a) (get_word μ2 a)).

(* Two-world memory ownership — Public cells as SyncVal, the rest as NonSyncVal *)
Definition interp_mem_with_public_memory `{sailGS2 Σ} (μ1 μ2 : Memory)
    (specs : list mem_cell) : iProp Σ :=
  [∗ list] spec ∈ specs,
    let a := cell_addr spec in
    if cell_pub spec
    then interp_ptstomem (width := 4) (SyncVal a) (SyncVal (get_word μ1 a))
    else interp_ptstomem (width := 4) (SyncVal a)
           (NonSyncVal (get_word μ1 a) (get_word μ2 a)).
```

The old `mem_spec := Val ty_word * bool` pair is gone (PLAN-spec-layer D18);
`cell_addr`/`cell_pub` are its two projections.

```coq
```

Note this body **ignores the list index** (and, in the public branch, `μ2`). Both
facts are load-bearing for the classed-existential path: index-independence is what
lets `big_opL_permutation` re-associate the resource list by publicness class, and
publicness-only dependence is why a per-group conversion needs no hypothesis about
the value slot. See `gen_implpre_mem_class` in **cfgver-endtoend-internals**.

## `something_memory` equivalence

```coq
Lemma something_memory `{sailGS2 Σ} μ1 μ2 (specs : list mem_cell)
    (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs specs)) :
  interp_mem_with_memory μ1 μ2 specs ⊣⊢
  interp_mem_with_public_memory μ1 μ2 specs.
```

Usage: `rewrite (something_memory data_specs HpubMem)` rewrites `interp_mem_with_memory`
to `interp_mem_with_public_memory` in the current Iris proof state (including hypothesis
types, since Iris environments are Coq terms).

## `instrsAndDataMemory_at` (data ANYWHERE) and `instrsAndDataMemory`

`instrsAndDataMemory_at` (2026-10-02) is the general form: its data premise is
`data_layout_ok start (length instrs) data_specs` — every cell in range, clear
of the code `[start, start+4|instrs|)`, cells pairwise disjoint
(`ForallOrdPairs data_cell_sep`). Proof: code bytes ++ data bytes are NoDup and
live, so a sub-multiset of `liveAddrs`; `big_sepL_submseteq` peels them off.
`contig_data_layout` derives `data_layout_ok` from the old contiguous premise,
and `instrsAndDataMemory` (below) is now that corollary. To prove
`data_layout_ok` for a layout of contiguous RUNS (e.g. code-adjacent data plus
an array behind a pointer), rewrite the cells to `GenProg.data_runs` with
`concretize_run_map` and apply `GenProg.data_layout_runs` — interval
conditions, closed by `lia` (worked example: `CheckScalarPtrResult.v`).

**The contiguity restriction was never in the trusted statement**
(`noninterferent_strong` takes a `mem_layout` of blocks at arbitrary addresses)
— only in this lemma's old premise. Real pointer arguments need no trusted change.

The contiguous form: data words occupy the `4*|data_specs|` bytes immediately
following the instruction region.

```coq
Lemma instrsAndDataMemory `{sailGS2 Σ} {μ1 μ2} ws_instrs data_specs instrs :
  (4 * N.of_nat (length instrs) + 4 * N.of_nat (length data_specs) < lenAddr)%N →
  mem_has_instrs μ1 (bv.of_N init_addr) ws_instrs instrs →
  mem_has_instrs μ2 (bv.of_N init_addr) ws_instrs instrs →
  (∀ i spec, data_specs !! i = Some spec →
    spec.1 = (init_addr + 4 * N.of_nat (length instrs) + 4 * N.of_nat i)%N) →
  mem_res2_without_leak μ1 μ2 ⊢ |={⊤}=>
    ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs ∗
    interp_mem_with_memory μ1 μ2 data_specs.
```

## `cfg_instrs_verified_with_mem` / `cfg_instrs_safe_with_mem`

Memory-aware variants of the (deleted 2026-10-02) register-only `cfg_instrs_verified` / `cfg_instrs_safe`; with `data_specs = []` they cover that case. The `ImplPre`
parameter also receives `interp_mem_with_public_memory μ1 μ2 data_specs` — they
exist because `ImplPre`'s Iris spatial context starts empty, so memory ownership
must be threaded through as a conjunct rather than framed from outside.

Their call patterns, implicit-argument asymmetry, and proof-body idioms are in the
**cfgver-endtoend-internals** skill (needed only when modifying the wiring lemmas).

## `cfg_instrs_endToEnd_with_memory`

Extension of `cfg_instrs_endToEnd` (→ **cfgver-endtoend** skill) for programs with data
memory. Requires:
- `data_specs : list mem_cell`
- `HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs data_specs)`
- `HDataAddrs` mapping spec indices to concrete addresses (contiguous after instruction region)
- `ImplPre` now also takes `interp_mem_with_public_memory μ1 μ2 data_specs`

The length bound is `4 * |instrs| + 4 * |data_specs| < lenAddr` (combined).

It is a corollary of **`cfg_instrs_endToEnd_gen`**, the one core end-to-end
theorem: same shape, but `HLayout : data_layout_ok init_addr (length instrs)
data_specs` instead of `HDataAddrs`, and the length bound covers the code only.
Use `_gen` directly for data that is not contiguous after the code.
