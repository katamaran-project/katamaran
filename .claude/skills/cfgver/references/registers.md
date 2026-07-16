# Two-world register machinery (reference)

Loaded on demand from parent skills (cfgver-gen-contract-internals,
cfgver-endtoend-internals) — never self-triggers. The two-world (γ1/γ2) register
ownership predicates used across the contract generator and the end-to-end wiring.

## Predicates

- `declare_public_registers γ1 γ2 public_registers : Prop` — a `Forall` stating the
  two register stores agree on every register in the public list. This is the
  *hypothesis* the caller provides about the initial states.
- `interp_gprs_with_public_registers γ1 γ2 public_registers : iProp` — Iris
  ownership of all GPRs where public registers carry `SyncVal` (one shared value)
  and the rest carry `NonSyncVal` (per-world values).
- `interp_gprs_with_registers` — the raw all-`NonSyncVal` form.
- `something_registers` — the equivalence rewriting between the two forms, given
  `declare_public_registers`. **Direction pitfall:** its LHS is the raw form; if the
  goal already shows `interp_gprs_with_public_registers`, rewrite right-to-left:
  `rewrite <- (something_registers HpubReg)`.
- `regPstsTo_sync_is_nonsync` — unifies `NonSyncVal v v` into `SyncVal v`; used by
  `gen_implpre` to upgrade a register known equal in both worlds into a synced one.
- `reg_convert : RegIdx -> option (Reg ty_xlenbits)` — index-to-register conversion
  underlying `gen_public_regs`.

## Helper lemmas

```coq
Lemma declare_pub_head_true r x rest γ1 γ2 :
  reg_convert r = Some x →
  declare_public_registers γ1 γ2 (gen_public_regs ((r, true) :: rest)) →
  read_register γ1 x = read_register γ2 x.

Lemma declare_pub_tail r pub rest γ1 γ2 :
  declare_public_registers γ1 γ2 (gen_public_regs ((r, pub) :: rest)) →
  declare_public_registers γ1 γ2 (gen_public_regs rest).
```

Pitfalls:
- `x` in `declare_pub_head_true` is implicit under `Set Implicit Arguments` — use
  `eapply` and let Coq infer it from the `reg_convert` hypothesis; `exact` fails.
- `declare_public_registers γ1 γ2 []` is proved `by constructor`: stdpp's
  `Forall_nil` is an **iff lemma**, not the constructor — `Forall_nil _` fails.
