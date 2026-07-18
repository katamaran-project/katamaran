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

## The generator call

```coq
gen_contract (init_addr : N)
             (reg_specs : list reg_spec)
             (mem_specs : list mem_full_spec)
             (instrs : list AST)
             (extra_exit_offs : list N)
             (ec : bv xlenbits -> bool)
             (fl : nat) : CFGVerifierContract
```

- `extra_exit_offs`: base-relative byte offsets of exit addresses **beyond** the
  fall-through one (always included automatically). Needed when control flow can
  leave the program other than by falling off the end — e.g. a branch whose taken
  target lies past the program (`jump_if_zero`). Straight-line programs pass `[]`.
- `fl` (fuel) must exceed the number of instruction steps actually executed —
  with slack (→ **cfgver-solve-vc** for the tight-fuel failure mode).

The full contract record (placement, exit terms, precondition assertion) is
assembled for you; to inspect or understand it, see **cfgver-contracts**.

## The end lemma: five premises (six for `_rel`)

The VC is one line (`vm_compute. solve_vc.` — residuals in **cfgver-solve-vc**).
The end lemma is `eapply gen_contract_noninterferent` (or `_param`/`_rel` for a
parametric base) with **five** side premises (`_rel` adds a sixth, `Hbound`,
right before `valid_contract`):

| Premise | What it demands | Typical discharge |
|---|---|---|
| `HND` | `NoDup (map reg_spec_idx reg_specs)` | `repeat constructor` / `vm_compute`-style |
| `HDataAddrs` | data word i sits at `init_addr + 4*|instrs| + 4*i` | case split per entry; `f_equal; lia` if base symbolic |
| `Hlen` | `init_addr + 4*|instrs| + 4*|mem_specs| < lenAddr` | `unfold lenAddr; lia` |
| *(`_rel` only)* `Hbound` | `init_addr + bound < lenAddr` | `exact` the premise you were given |
| `HexitOffs` | `exitCond` true at fall-through + every extra exit offset | `Forall` constructors + `vm_compute` (see multi-offset note below) |
| `valid_contract` | the `ValidCFGVerifierContract` VC | the one-line VC lemma — **discharge this ONE FIRST, see below** |

Conclusion: `noninterferent_strong init_addr instrs exitCond reg_specs mem_specs`
(or, for `_rel`, over `map (concretize_reg/mem init_addr) specs_rel`).

`HexitOffs` is where `cfg_exitCond` (unused by the symbolic VC) gets reconnected to
the contract's exit-term table — see **cfgver-contracts** for that design subtlety.
If `extra_exit_offs` is non-empty (e.g. `jump_if_zero`'s `[8%N]`), `HexitOffs` is a
**multi-element** `Forall` — `constructor; [apply pcOutOfInstrs_fallthrough |
constructor]` only closes the single-element case (`extra_exit_offs = []`, the
common case). For each extra offset you need one more `constructor` split plus a
hand-written exit-fact proof, e.g. for offset `8`:
```coq
constructor.
+ apply pcOutOfInstrs_fallthrough.
+ constructor; [ | constructor ].
  unfold pcOutOfInstrs_exitCond, bv.ugeb, bv.uleb.
  apply N.leb_le.
  rewrite bv.of_N_add.                 (* collapses bv.add(of_N ia)(of_N o) into of_N(ia+o) — see bv-pitfalls *)
  (* … reduce both sides to bv.bin (bv.of_N _) via bv.bin_of_N_small
     (needs a `< bv.exp2 xlenbits` side bound, per bv-pitfalls), then lia. *)
```

### CRITICAL — discharge `valid_contract` FIRST, not last

`eapply gen_contract_noninterferent(_param/_rel)` leaves several existential
metavariables shared across ALL the goals (from unifying `reg_specs`/`mem_specs`/
`instrs`/`exitCond`/`fuel` against the conclusion). Solving the OTHER bullets
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
eapply gen_contract_noninterferent_param.
5: exact (valid_<x>_cfg_contract_param init_addr). (* MUST come first *)
- apply Prelude.nodup_fixed; reflexivity.                        (* HND *)
- intros ? ? Hlk; rewrite lookup_nil in Hlk; discriminate.       (* HDataAddrs *)
- cbn. lia.                                                      (* Hlen *)
- constructor; [apply pcOutOfInstrs_fallthrough | constructor].  (* HexitOffs *)
Qed.
```
(`6: exact (...)` for `_rel`, since it has the extra `Hbound` premise.) This is
not a new invention — the non-parametric `gen_contract_noninterferent` call
sites in `Results.v` already used this exact "do the last one first" ordering
(with a TODO comment); it was simply missed when writing the new parametric
lemmas.

## Parametric base

Two generator variants build a contract over a *symbolic* placement term
`term_var "p"` (`Σ = ["p"∷ty_xlenbits]`) instead of a concrete
`term_val (bv.of_N init_addr)` — the base stays a genuine variable, so the VC is
proved ONCE for `∀ init_addr`, not per concrete address:

- **`gen_contract_param`** — for reg/mem specs whose values are
  BASE-INDEPENDENT (constants or existentials; same `reg_spec`/`mem_full_spec`
  vocabulary as `gen_contract`). Adds a base-bound precondition conjunct
  (`unsigned p + 4*len ≤ lenAddr`) that the fetch upper-bound needs.
- **`gen_contract_rel`** — for reg/mem specs whose values are BASE-RELATIVE:
  `param_val = PVExist | PVConst v | PVBaseOff k` (meaning `p+k`), needed when a
  register holds a base-relative address (e.g. cmovznz4's `A1 = p+116`) or a
  data word's OWN address shifts with the base (e.g. countdown_mem's counter at
  `p+16`). Takes an extra `bound : N` param (≥ max accessed byte offset + 4) and
  builds `reg_spec_rel`/`mem_spec_rel` lists instead of the plain ones.

**Bridges**: `gen_contract_noninterferent_param`/`_rel` (in `EndToEnd.v`) mirror
`gen_contract_noninterferent`'s premises (see table above) and instantiate the
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
`cmovznz4_noninterferent`/`countdown_mem_noninterferent`):
```coq
assert (Hr : concrete_reg_specs = map (concretize_reg init_addr) specs_rel)
  by (vm_compute; reflexivity).
assert (Hm : concrete_mem_specs = map (concretize_mem init_addr) mem_specs_rel)
  by (vm_compute; reflexivity).
rewrite Hr Hm.
apply <x>_noninterferent_param.
unfold init_addr, lenAddr; lia.
```

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
