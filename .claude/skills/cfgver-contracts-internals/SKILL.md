---
name: cfgver-contracts-internals
description: >
  Internal machinery of the Katamaran CFGVer contract generator — library skill,
  normally reached from cfgver-contracts. Consult when MODIFYING or extending the
  generator itself, not when merely specifying a program: the gen_reg_asn / gen_pre /
  gen_mem_asn / gen_mem_pre assertion builders, gen_public_regs and reg_convert, the
  once-and-for-all gen_implpre lemma (Iris register ownership entails the interpreted
  gen_pre), declare_public_registers, and the declare_pub_head_true /
  declare_pub_tail helpers with their implicit-argument and Forall_nil pitfalls.
  For USING gen_contract see cfgver-contracts.
---

# Contract-generator internals

How `gen_contract`'s pieces are built and proved. Users specifying a program need
only **cfgver-contracts**; this skill is for changing the machinery (new spec forms,
new assertion shapes, extending `gen_implpre`).

All definitions live in `Examples.v` inside `WithAsnNotations`.

## Assertion builders

```coq
Definition gen_reg_asn {Σ} (s : reg_spec) : Assertion Σ :=
  let '(r, is_pub, opt_v) := s in
  match opt_v with
  | Some v => r ↦ᵣ term_val ty_xlenbits v
  | None =>
    asn.exist "v" ty_xlenbits
      (if is_pub then r ↦ᵣ term_var "v" ∗ secLeakvar "v"
                 else r ↦ᵣ term_var "v")
  end.

Definition gen_pre {Σ} (specs : list reg_spec) : Assertion Σ :=
  List.fold_right (fun s acc => gen_reg_asn s ∗ acc) ⊤ specs.
```

`gen_mem_asn` / `gen_mem_pre` follow the same shape over `mem_full_spec` with `↦ₘ`.
`gen_pre [] = ⊤`, so the empty-spec case degenerates gracefully.

```coq
(* Public register list: entries with is_public = true, converted to Reg *)
Definition gen_public_regs (specs : list reg_spec) : list {x : Ty & 𝑹𝑬𝑮 x} :=
  base.omap (fun '(r, pub, _) =>
    if pub then option_map (@existT Ty 𝑹𝑬𝑮 ty_xlenbits) (reg_convert r)
    else None) specs.
```

## `gen_implpre` — the once-and-for-all `ImplPre`

```coq
Lemma gen_implpre `{sailGS2 Σ}
    (specs : list reg_spec) (γ1 γ2 : RegStore)
    {Σ0} (ι : Valuation (Σ0 ▻ "a"∷ty_xlenbits))
    (HpubReg : declare_public_registers γ1 γ2 (gen_public_regs specs))
    (HND : NoDup (map reg_spec_idx specs)) :
  interp_gprs_with_public_registers γ1 γ2 (gen_public_regs specs) ⊢
  asn.interpret (gen_pre specs) ι.
```

Converts Iris register ownership into the interpreted symbolic `gen_pre`. For public
registers it uses `regPstsTo_sync_is_nonsync` to unify `NonSyncVal v v` into
`SyncVal v`. The `ι` context is generalized over `Σ0` (backward-compatible with
`[ctx]`) so the same lemma serves the parametric-base bridges. A ~130-line Iris
induction — extensions should reuse it (cf. the concretize trick in the `_rel`
bridge) rather than re-prove it.

## Register machinery

The two-world register predicates `gen_implpre` builds on
(`declare_public_registers`, `interp_gprs_with_(public_)registers`,
`something_registers`, `regPstsTo_sync_is_nonsync`, the `declare_pub_*` helpers and
their pitfalls) are documented in `.claude/skills/cfgver/references/registers.md` —
read that file when working on this layer.
