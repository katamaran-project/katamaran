---
name: cfgver-contracts
description: >
  How to SPECIFY a program for Katamaran CFGVer verification — the gen_contract user
  guide. Use when declaring which registers or memory words are public, private, or
  pinned to a concrete value: reg_spec (RegIdx * is_public * option value),
  mem_full_spec (address * is_public * option value), extra_exit_offs for
  non-fall-through exits, the gen_contract call itself, secLeakvar, and the five side
  premises of gen_contract_noninterferent (NoDup, data-address layout, length bound,
  exit offsets, the VC). NOT for the generator's internal machinery (gen_reg_asn /
  gen_implpre — cfgver-contracts-internals) and NOT for the Iris memory resources
  supplied at proof time (interp_mem_* — cfgver-memory).
---

# Specifying a program: the `gen_contract` user guide

Everything you *write* to put a new program through the verifier. How the generator
works inside is **cfgver-contracts-internals**; the Iris resources you supply when
*proving* are **cfgver-memory** (data) and **cfgver-endtoend** (wiring).

## Register specs

```coq
Definition reg_spec : Type := RegIdx * bool * option (Val ty_xlenbits).
```

Per register `(r, is_public, opt_v)`:
- `opt_v = Some v` — the register is **pinned**: precondition asserts it holds
  exactly `v` (no existential, no leak permission).
- `opt_v = None, is_public = true` — **public**: existentially quantified value
  with `secLeakvar`, i.e. attacker-visible / allowed to influence leakage.
- `opt_v = None, is_public = false` — **private**: existentially quantified secret;
  must NOT influence leakage — that is what the verifier checks.

## Memory-word specs (contract side)

```coq
Definition mem_full_spec : Type :=
  Val ty_xlenbits * bool * option (Val ty_xlenbits).
```

Same triple semantics for a data word at the given address (`↦ₘ` instead of `↦ᵣ`).
These generate the `gen_mem_pre` conjunct of the precondition. Data words must sit
**contiguously right after the instruction region** (see the `HDataAddrs` premise
below and **cfgver-memory** for the proof-time counterpart).

## The contract

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
  leave the block other than by falling off the end — e.g. a branch whose taken
  target lies past the block (`jump_if_zero`). Register-straight-line programs
  pass `[]`.
- `fl` (fuel) must exceed the number of instruction steps actually executed.
- Precondition assembled: `asn_init_pc (bv.of_N init_addr) ∗ gen_pre reg_specs ∗
  gen_mem_pre mem_specs`.

## Discharging the VC and the end lemma

The VC is one line: `Proof. vm_compute. solve_vc. Qed.`
(residual patterns → the **cfgver** hub).

The end lemma is `eapply gen_contract_noninterferent` with **five** side premises:

| Premise | What it demands | Typical discharge |
|---|---|---|
| `HND` | `NoDup (map reg_spec_idx reg_specs)` | `vm_compute`-style / `repeat constructor` |
| `HDataAddrs` | data word i sits at `init_addr + 4*|instrs| + 4*i` | case split per entry; `f_equal; lia` if base symbolic |
| `Hlen` | `init_addr + 4*|instrs| + 4*|mem_specs| < lenAddr` | `unfold lenAddr; lia` |
| `HexitOffs` | `exitCond` true at fall-through + every extra exit offset | `Forall` constructors + `vm_compute` |
| `valid_block` | the `ValidCFGVerifierContract` VC | the one-line VC lemma |

Conclusion: `noninterferent_strong init_addr instrs exitCond reg_specs mem_specs`.

## Parametric base

For a contract over a *symbolic* base address (`term_var "p"`), the `_rel` variants
exist (`gen_contract_rel`, `reg_spec_rel` with `PVBaseOff` offsets,
`gen_contract_noninterferent_rel`) — not yet covered by a skill; see the
"PARAMETRIC-BASE SUPPORT — READING GUIDE" blocks in `Examples.v` and memory
`project-cfgver-symbolic-base-poc`.
