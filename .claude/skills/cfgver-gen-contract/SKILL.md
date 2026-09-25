---
name: cfgver-gen-contract
description: >
  User guide for gen_contract — Katamaran CFGVer's contract GENERATOR — and its
  symbolic/parametric-base variants gen_contract_param / gen_contract_rel. Use
  when specifying a program via spec lists: reg_spec (RegIdx * is_public *
  option value), mem_full_spec (address * is_public * option value), the
  base-relative param_val/reg_spec_rel/mem_spec_rel vocabulary (PVBaseOff k =
  base+k), public/private/pinned semantics, extra_exit_offs for non-fall-through
  exits, the 7-argument gen_contract call, and the five-or-six side premises of
  gen_contract_noninterferent(_param/_rel) (NoDup, data-address layout, length
  bound, exit offsets, base bound, the VC). ALSO use when MIGRATING an existing
  concrete-base example/contract to a parametric (∀ init_addr) base, or planning
  that migration across several examples — this is the gen_contract_param/_rel
  recipe, not a from-scratch design question. Trigger on the "discharge
  valid_contract FIRST, not last" bullet-ordering gotcha too: a
  gen_contract_noninterferent(_param/_rel) proof whose Qed hangs, fails with
  "Attempt to save an incomplete proof (there are remaining open goals)", or
  behaves differently depending on which imports are in scope — a wrong-
  unification bug easily mistaken for an environment/memory problem (see
  rocq-compile-oom for that angle, but this skill has the actual fix). The
  interface is spec lists only — no assertions. NOT for hand-writing contract
  assertions or secLeakvar (cfgver-contracts), the generator's internal machinery
  (cfgver-gen-contract-internals), or proof-time Iris memory resources
  (cfgver-memory).
---

# Specifying a program with `gen_contract`

Everything you *write* to put a new program through the verifier using the
generator. What a contract *is* (the record, hand-writing one) is
**cfgver-contracts**; how the generator works inside is
**cfgver-gen-contract-internals**; the full new-example workflow is
**cfgver-new-example**.

## Register specs

```coq
Definition reg_spec : Type := RegIdx * bool * option (Val ty_xlenbits).
```

Per register `(r, is_public, opt_v)`:
- `opt_v = Some v` — the register is **pinned**: it holds exactly `v` (no leak
  permission).
- `opt_v = None, is_public = true` — **public**: arbitrary value, attacker-visible /
  allowed to influence leakage.
- `opt_v = None, is_public = false` — **private**: arbitrary secret; must NOT
  influence leakage — that is what the verifier checks.

You never write assertions here — the generator emits them (public compiles to a
`secLeakvar` conjunct under the hood). For the assertion-level vocabulary — needed
only for hand-written contracts — see **cfgver-contracts**.

## Memory-word specs (contract side)

```coq
Definition mem_full_spec : Type :=
  Val ty_xlenbits * bool * option (Val ty_xlenbits).
```

Same triple semantics for a data word at the given address. These become the
contract's memory precondition (assembled for you). Data words must sit
**contiguously right after the instruction region** (see the `HDataAddrs` premise
below and **cfgver-memory** for the proof-time counterpart).

### Byte-granular cells, for `lbu` programs (`gen_contract_rel_bytes`)

A byte load calls `mem_read 1` and so consumes a `ptstomem 1` chunk. Width is part
of the predicate index (`Sig.v`), so `ptstomem 1` and `ptstomem 4` are DIFFERENT
predicates and a resident word chunk cannot discharge a byte consume — the chunk
matcher has no split rule. Use `gen_contract_rel_bytes`, which takes a THIRD
data list whose entries are read byte-wise:

```coq
gen_contract_rel_bytes (init_addr) (reg_specs) (mem_specs)
                       (byte_mem_specs)      (* <-- these get 4 x ptstomem 1 each *)
                       (instrs) (bound) (fl)
```

Both data lists are `list mem_spec_rel` — same type, same `PVExist`/`PVConst`/
`PVBaseOff` vocabulary. **Byte expansion is opt-in PER ENTRY** so the 4× chunk
multiplier is paid only where a byte access needs it, and **the declaration unit
stays a WORD**: a byte-expanded entry still describes the 4 bytes at a word-aligned
address, so stride stays 4, `HDataAddrs` is unchanged, and the trusted statement
layer (`mem_full_spec`, `gen_init_mem`, `declare_*`) is untouched — on that side
the two lists are just concatenated, `mem_specs ++ byte_mem_specs` (keep
`mem_specs` first and both blocks contiguous). So 32 secret bytes are **8 spec
entries**, not 32.

An existential (`PVExist`) entry costs **one** logic variable, not four: the entry
declares one `ty_xlenbits` variable and the four chunks are byte projections
(`term_word_byte j`) of it. This is a performance decision, measured — four
independent byte variables cost +43% `vm_compute` and +56% `Qed` at 32 bytes, and
turn a VC doubling-slope of 1.02 into 1.39. The general rule behind it: cost tracks
the size of state TRANSPORTED PER WORLD EXTENSION, and `|Σ|` feeds the
`Sub`/`Valuation` rebuilt at every extension — so prefer fewer, larger symbolic
objects even when the small ones have smaller individual terms. The same rule is
why speeding up heap LOOKUP is a dead end (≤7%) while shrinking the heap is not.

Public existential entries are fine to byte-expand: the precondition asks for
`secLeakvar` on the *word* variable, which is exactly the SyncVal word
`interp_mem_with_public_memory` provides.

`gen_contract_rel` itself is deliberately NOT refactored to delegate to the bytes
variant — nine `vm_compute` VC proofs reduce through it, so the duplication is
cheaper than the perturbation.

`Tables.v` supplies `LBU rd rs imm` (= `LOAD imm rs rd true BYTE`; the `true` is
the zero-extend flag, and `LW` passes `false`). Status: the VC side works —
`check_scalar` loop 1 verifies at N = 32 — but the `EndToEnd.v` Iris wiring that
would give a byte program a noninterference END theorem is **not written yet**
(`PLAN-byte-memory.md` §5.3, §10). Residual shapes a byte program leaves →
**cfgver-solve-vc**.

## The generator call

```coq
gen_contract (init_addr : N)
             (reg_specs : list reg_spec)
             (mem_specs : list mem_full_spec)
             (instrs : list AnnotInstr)
             (fl : nat) : CFGVerifierContract
```

The exit is always the fall-through `base + 4*|instrs|` (`cfg_exit :=
exit_of_off base (4 * |instrs|)`); no generator takes an exit argument.

`instrs` used to be `list AST`; it is `list AnnotInstr` since the AnnotInstr
migration (PLAN-annotinstr.md, Phase 1). This is invisible to every existing
caller: a plain `_instrs : list AST` value (e.g. `cmovznz4_instrs`) still passes
straight in, via a non-Local `Coercion` in `Verifier.v` (`AST -> AnnotInstr`
per-element, plus a second `list AST -> list AnnotInstr` coercion for reusing an
already-typed list wholesale — both needed, see **cfgver-executor**). All six
builders (`gen_contract(_param/_rel/_u/_rel_classed/_rel_bytes)`) took the same
change; the four that compute an exit offset or bound from `length instrs`
switched to `length (strip instrs)`, since ghost entries occupy no address.

- **One exit only.** A program whose control flow leaves other than by falling
  off the end is a SEGMENT: use `gen_seg_contract` (`GenSegment.v`), which takes
  its one `target : N`. Recommended discipline: cut at the join point so there is
  one exit (`jump_if_zero` got a trailing `NOP` for this). History (the removed
  `extra_exit_offs`/`ec` arguments): `plans/PLAN-exit-targets.md`.
- `fl` (fuel) must exceed the number of instruction steps actually executed —
  with slack (→ **cfgver-solve-vc** for the tight-fuel failure mode).

The full contract record (placement, exit terms, precondition assertion) is
assembled for you; to inspect or understand it, see **cfgver-contracts**.

## The end lemma

The VC is one line (`vm_compute. solve_vc.` for a concrete base, or
`intros; vm_compute; solve_vc; solve_symbase_fetch.` for a parametric base —
residuals in **cfgver-solve-vc**).

### Common case: the `_simple` bridges (prefer these)

Every generator contract exits at the fall-through, and the bridges in
`EndToEnd.v` conclude `noninterferent_strong init_addr instrs (init_addr + 4 *
N.of_nat (length instrs)) …`, discharging the exit fact internally:

- **`gen_contract_noninterferent_param_simple`** (register-only, `mem_specs = []`):
  premises are just `HND` (`apply Prelude.nodup_fixed; reflexivity`), a
  simplified `Hlen` (`cbn; lia`), and the VC.
- **`gen_contract_noninterferent_rel_classed_simple`** (base-relative, possibly
  with data memory, data block in CLASSED form — the default for new work): for a
  contract built with `gen_contract_rel_classed` (see below). Premises `HND`,
  `HDataAddrs`, `Hlen`, `Hbound`, and the VC.
- **`gen_contract_noninterferent_rel_bytes_simple`** — the same premises for a
  BYTE-granular data block (`gen_contract_rel_bytes`).

The classed bridge's unclassed predecessor `gen_contract_noninterferent_rel_simple`
(over `gen_contract_rel`) was **deleted 2026-08-18** as dead — stage 0 of
`plans/PLAN-unify-generators.md`. Its conclusion was byte-identical to the classed
one's, which is why switching an example between them was a one-identifier change
in each of its two files and never touched the trusted statement surface. Note the
builder `gen_contract_rel` itself was KEPT: it has no example users but 26 rig
users, and is the unclassed control arm for the `|Σ|` cost measurements.

For these three the **"discharge valid_contract FIRST" ordering hazard below
cannot arise** (only `fuel` floats, and it appears only in the VC premise — so
premises may be discharged in any order). Typical proof:

```coq
Proof.
  intros Hbound.
  eapply gen_contract_noninterferent_param_simple.
  - apply Prelude.nodup_fixed; reflexivity.
  - cbn; lia.
  - exact (valid_<prog>_cfg_contract_param init_addr).
Qed.
```

Since `plans/PLAN-exit-targets.md` there is no difference between the general and
`_simple` forms regarding exits: `_param_simple` / `_u_simple` are aliases of
`_param` / `_u`, and the `_rel_*_simple` ones are thin delegations onto `_u`.

### General bridges: premises

The general bridges are `gen_contract_noninterferent_param` (register-only) and
`gen_contract_noninterferent_u` (base-relative data, word + byte lists). Their
premises:

| Premise | What it demands | Typical discharge |
|---|---|---|
| `HND` | `NoDup (map reg_spec_idx reg_specs)` | `repeat constructor` / `vm_compute`-style |
| `HDataAddrs` | data word i sits at `init_addr + 4*|instrs| + 4*i` | case split per entry; `f_equal; lia` if base symbolic |
| `Hlen` | `init_addr + 4*|instrs| + 4*|mem_specs| < lenAddr` | `unfold lenAddr; lia` |
| *(`_u` / `_rel_*` only)* `Hbound` | `init_addr + bound < lenAddr` | `exact` the premise you were given |
| `valid_contract` | the `ValidCFGVerifierContract` VC | the one-line VC lemma — **discharge this ONE FIRST, see below** |

Conclusion: `noninterferent_strong init_addr instrs (init_addr + 4 * N.of_nat
(length instrs)) reg_specs mem_specs` (or, for `_u`, over `map
(concretize_reg/mem init_addr) specs_rel`). There is no exit premise: the exit
fact is discharged inside the bridge.

### CRITICAL — discharge `valid_contract` FIRST, not last

**Scope since `plans/PLAN-exit-targets.md`:** the historical instances involved a
floating exit condition, which no longer exists; `_param` and all `_simple`
bridges now leave only `fuel` floating (VC premise only), so the hazard applies at
most to a direct `eapply gen_contract_noninterferent_u` whose data lists /
`bound` / `fuel` are not pinned by name. The advice below is kept as a cheap
precaution.

An `eapply` can leave existential metavariables shared across ALL the goals
(from unifying spec lists / `bound` / `fuel` against the conclusion). Solving the OTHER bullets
first lets their tactics (especially `constructor`) resolve those shared
metavariables to the WRONG instantiation. The symptom is NOT a clean tactic
failure — it's a `Qed` that either **hangs indefinitely** or fails with a
bizarre, ambient-import-dependent error (observed directly: hangs with the
project's Iris/Equations imports in scope, but fails fast with a clean "no
subterm found" error without them — same underlying bug, different symptom
depending on which `rewrite` engine, plain Coq's or transitively-imported
SSReflect's, is active). This cost a multi-hour debugging session that initially
looked like a memory/OOM/environment problem (see **rocq-compile-oom**) before
being traced here.

**Fix: always discharge the LAST premise (`valid_contract`) by explicit goal
number, before any bullet:**
```coq
eapply gen_contract_noninterferent_u.
5: exact (valid_<x>_cfg_contract_param init_addr). (* MUST come first *)
- ...                                                            (* HND *)
- ...                                                            (* HDataAddrs *)
- ...                                                            (* Hlen *)
- ...                                                            (* Hbound *)
Qed.
```
No tracked call site needs this any more (all use `_simple` or name-pinned
`eapply`s); history in `plans/PLAN-exit-targets.md`.

## Parametric base

These variants build a contract over a *symbolic* placement term
`term_var "p"` (`Σ = ["p"∷ty_xlenbits]`) instead of a concrete
`term_val (bv.of_N init_addr)` — the base stays a genuine variable, so the VC is
proved ONCE for `∀ init_addr`, not per concrete address.

**Since 2026-08-18 there is only ONE real implementation, `gen_contract_u`**
(`PLAN-unify-generators.md` stage 3); everything below it is a one-line wrapper.
Which name you *call* is an ergonomics choice, but a change to the contract record
now touches `gen_contract_u` alone.

- **`gen_contract_u`** — the unified builder:
  `init_addr reg_specs word_data byte_data instrs bound fl`,
  all over the base-relative `param_val` vocabulary, classing by default.
  **Granularity is carried by WHICH LIST an entry is in** — `word_data` gets one
  `ptstomem 4` chunk per key, `byte_data` gets four `ptstomem 1`. There is
  deliberately no `gran` field on entries: a class's grouped existential width
  must be computable from a list you induct on directly, and a
  filtered-and-projected list needs a dependent transport across a type index (the
  width-index trap, `core-executor-internals` §6). Keep word cells first; the
  trusted side sees `word_data ++ byte_data`.
- **`gen_contract_param`** — wrapper for a **register-only** program whose register
  values are BASE-INDEPENDENT, keeping the plain `reg_spec` (`None` / `Some v`)
  vocabulary rather than making you write `PVExist` / `PVConst v`. It absorbs the
  `reg_spec_to_rel` translation *and* fixes `bound = 4·|instrs|`, which is why it
  is worth keeping. **Four arguments** — `init_addr reg_specs instrs fl`
  (the exit arguments went 2026-09-25); the `mem_full_spec` list it used to accept was
  removed (all 15 call sites passed `[]`). Data memory → call `gen_contract_u`.
- **`gen_contract_rel`** — for reg/mem specs whose values are BASE-RELATIVE:
  `param_val = PVExist | PVConst v | PVBaseOff k` (meaning `p+k`), needed when a
  register holds a base-relative address (e.g. cmovznz4's `A1 = p+116`) or a
  data word's OWN address shifts with the base (e.g. countdown_mem's counter at
  `p+16`). Takes an extra `bound : N` param (≥ max accessed byte offset + 4) and
  builds `reg_spec_rel`/`mem_spec_rel` lists instead of the plain ones.
- **`gen_contract_rel_classed`** — same signature and same statement strength as
  `gen_contract_rel`, but the data block emits **one existential per publicness
  class** instead of one per `PVExist` entry: an N-cell class becomes a single
  `bv (xlenbits * N)` variable whose cells are `bvtake`/`bvdrop` slices. This is
  *equivalent*, not weaker (N independent words are in bijection with one N-word
  vector), and it exists because `|Σ|` is the dominant VC cost driver — measured
  quadratic, and ~30–46× more expensive per unit than a chunk. **This is the
  default choice for a new base-relative example with data memory.** Its
  bridge is `gen_contract_noninterferent_rel_classed_simple` (above).

  Two things to know. **The win scales with declared cell count**: 3.31× at 32
  cells, but only ~1.19× at 12 — so for a handful of cells it is close to a
  wash. And **the heap order changes** to pinned, then public, then private,
  rather than spec order; `consume` is order-sensitive, so a VC residual shape
  can in principle move. In practice it did not for any of the four migrated
  examples, because their data blocks are homogeneous (all-private `PVExist`),
  which makes the reordering the identity. Expect to have to look only when a
  data block genuinely MIXES pinned/public/private cells.

  There is deliberately **no classed counterpart of `gen_contract_rel_bytes`**.
  For `gen_contract_param` the situation CHANGED on 2026-08-18: it is now itself a
  classed builder, delegating to `gen_contract_rel_classed` at `mem_specs = []`
  (`PLAN-unify-generators.md` stage 1). What stays impossible is classing a
  **non-empty concrete `mem_full_spec` block** — the two sides' existential widths
  are `mem_class_width (mem_rel_keys L)` and
  `mem_class_width (mem_full_keys (map (concretize_mem ia) L))`, equal only
  propositionally, so the bridge would need a dependent transport across a type
  index (`core-executor-internals` §6; note at `GenContract.v:536`). That case is
  now *unrepresentable* rather than merely unimplemented, since the parameter is
  gone. The deeper reason it could never have worked: `mem_full_spec` carries
  ABSOLUTE addresses and the classed block needs base-relative `mem_spec_rel`
  offsets, and you cannot translate one to the other without knowing the base.

**Bridges**: `gen_contract_noninterferent_param`/`_rel` (in `EndToEnd.v`) take the
premises in the table above and instantiate the
placement valuation at `ι = ["p" ↦ SyncVal (bv.of_N init_addr)]`. For `_rel`, the
conclusion is stated over `map (concretize_reg/concretize_mem init_addr)
specs_rel` (`concretize_reg`/`concretize_mem` send a `PVBaseOff k` to
`Some (bv.of_N (init_addr+k))` at a chosen concrete base).

**Concrete corollaries are free once the parametric lemma is proved** — no new
`vm_compute`. Plain `gen_contract_param` case (statement identical to the
concrete target, e.g. `countdown_noninterferent`):
```coq
apply <x>_noninterferent_param.
unfold init_addr, lenAddr; lia.
```
`gen_contract_rel` case (concrete specs need proving equal to the concretized
`_rel` specs first, via a `vm_compute`-computable equality — e.g.
`cmovznz4_noninterferent`/`countdown_mem_noninterferent`): use the
**`ni_rel_corollary`** tactic notation (in `EndToEnd.v`), which folds the whole
prove-equal / rewrite / apply / discharge-bound ritual:
```coq
ni_rel_corollary <x>_noninterferent_param <x>_reg_specs_rel <x>_mem_specs_rel init_addr.
```
It reads the concrete base from the goal, so the LAST argument is just the
base-*definition* to unfold for the final `lia` — pass `init_addr` for the
`= 0` corollary or a nonzero base def (e.g. `cmovznz4_start`) for a
fixed-address one (`cmovznz4_noninterferent_at_start`); the parametric lemma is
the same. Under the hood it still does the two `vm_compute; reflexivity`
spec-equalities, `rewrite`, `apply <x>_noninterferent_param`, then
`unfold <base_def>, lenAddr; lia`.

**Register choice for base-relative memory addressing.** RISC-V's `X0` is
architecturally hardwired to the constant `0` (`Machine.v`'s `rX`/`wX` special-
case register index `00000` to `[bv 0]` / a no-op write) — a `LOAD`/`STORE`
computing its address via `X0 + imm` is an ABSOLUTE address `imm`, regardless of
where the program is loaded, and CANNOT be made base-relative by any contract-
level trick. To make a data word move WITH the base (so `gen_contract_rel`'s
contiguous-layout `HDataAddrs` premise can hold at any base), the address must
instead be computed off a general register pre-initialized to the base
(`reg_spec_rel` entry with `PVBaseOff 0`) — a genuine INSTRUCTION-STREAM change
(not just a contract/proof-layer one) when migrating a program originally
written against `X0` (done for `countdown_mem`: `X0` → a dedicated `X2`).
