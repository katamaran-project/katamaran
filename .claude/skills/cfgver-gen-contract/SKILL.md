---
name: cfgver-gen-contract
description: >
  User guide for gen_contract — Katamaran CFGVer's contract GENERATOR. Use when
  specifying a program via spec lists: reg_spec (RegIdx * is_public * option value),
  mem_full_spec (address * is_public * option value), public/private/pinned
  semantics, extra_exit_offs for non-fall-through exits, the 7-argument
  gen_contract call, and the five side premises of gen_contract_noninterferent
  (NoDup, data-address layout, length bound, exit offsets, the VC). The interface
  is spec lists only — no assertions. NOT for hand-writing contract assertions or
  secLeakvar (cfgver-contracts), the generator's internal machinery
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

## The end lemma: five premises

The VC is one line (`vm_compute. solve_vc.` — residuals in **cfgver-solve-vc**).
The end lemma is `eapply gen_contract_noninterferent` with **five** side premises:

| Premise | What it demands | Typical discharge |
|---|---|---|
| `HND` | `NoDup (map reg_spec_idx reg_specs)` | `repeat constructor` / `vm_compute`-style |
| `HDataAddrs` | data word i sits at `init_addr + 4*|instrs| + 4*i` | case split per entry; `f_equal; lia` if base symbolic |
| `Hlen` | `init_addr + 4*|instrs| + 4*|mem_specs| < lenAddr` | `unfold lenAddr; lia` |
| `HexitOffs` | `exitCond` true at fall-through + every extra exit offset | `Forall` constructors + `vm_compute` |
| `valid_contract` | the `ValidCFGVerifierContract` VC | the one-line VC lemma |

Conclusion: `noninterferent_strong init_addr instrs exitCond reg_specs mem_specs`.

`HexitOffs` is where `cfg_exitCond` (unused by the symbolic VC) gets reconnected to
the contract's exit-term table — see **cfgver-contracts** for that design subtlety.

## Parametric base

For a contract over a *symbolic* base address, the `_rel` variants exist
(`gen_contract_rel`, `reg_spec_rel` with `PVBaseOff` offsets,
`gen_contract_noninterferent_rel`) — not yet covered by a skill; see the
"PARAMETRIC-BASE SUPPORT — READING GUIDE" blocks in `GenContract.v` and memory
`project-cfgver-symbolic-base-poc`.
