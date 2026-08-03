---
name: secret-data-walls
description: >
  The observation boundary in Katamaran's relational verifier: secret (NonSyncVal)
  data is fine as a VALUE but collapses to False the moment it reaches a formula or
  secLeak — `formula_bool`, `formula_relop`, and `secLeak` all map NonSyncVal ⇒
  False (Formulas.v). Explains why `term_eq`/`relop` on secret data is safe as a
  value yet fatal as a branch / path / publicness condition, and why canonical forms
  for secret computations should stay in pure `bv` arithmetic (no relop, no bool) to
  be structurally immune. Read this when a VC over secret data unexpectedly reduces
  to False, before branching on or comparing secret values, or when choosing between
  relop/bool and pure-`bv` forms for secret-dependent code (e.g. constant-time
  crypto). Framework-wide (theories/); assumes the `relval-model` value model; the
  `secLeakvar` contract permission itself lives in `cfgver-contracts`. A library skill.
---

# The secret-data observation walls

Secrets may freely *exist* as values (see **`relval-model`**: `NonSyncVal` is
contagious but never crashes). The model forbids *observing* them. Three sites turn
a `NonSyncVal` into `False` — this is the noninterference boundary. All in
`theories/Syntax/Formulas.v`:

| Site | On `NonSyncVal` | Meaning |
|------|-----------------|---------|
| `formula_bool t` (line 142) | `⇒ False` | can't take a branch / assume a path condition that depends on a secret |
| `formula_relop op t1 t2` (line 147) | `⇒ False` | can't assert a secret-dependent comparison |
| `secLeak rv` (line 117) | `SyncVal ⇒ True`, `NonSyncVal ⇒ False` | value declared public; a secret one is a leak |

`secLeakOtherDef` (Formulas.v:129): `secLeak rv ↔ rv = SyncVal (projLeft rv)`. In
CFGVer the `secLeakvar "v"` assertion is the *permission* that makes `"v"` public;
its **absence** is what makes a value secret (see **`cfgver-contracts`**).

## `term_eq` / `relop` on secrets — safe as a VALUE, fatal as a FORMULA

`term_eq = term_binop (bop.relop bop.eq)`, denoting `liftBinOp (eval_relop_val eq)`.
On a secret it yields a **`NonSyncVal bool`** — it does *not* crash. But that bool
is lethal the instant it is used as:

- a branch / path condition → `formula_bool` → `False`;
- a relational comparison formula → `formula_relop` → `False`;
- a publicness check → `secLeak` → `False`.

This is exactly right for **constant-time** code: CT idioms compute comparisons
*as bits* and feed them into arithmetic masks, never branching on them. So a
comparison-derived bit on secret data is fine *as long as it stays a value*.

## The wall fires on ANY `if:` — including one that only materialises a value

The walls govern *formulas*, and the symbolic executor turns **every** μSail
`stm_if` into one. That includes branches that make no observation whatsoever —
so a wall hit is not by itself evidence that the program leaks. It may only mean
the *model* expressed a value computation as a branch.

**Worked precedent (fixed 2026-07-27): RISC-V `SLT`/`SLTU`/`SLTI`/`SLTIU`.**
`RiscvPmp/Machine.v`'s `fun_bool_to_bits` used to be
`if: x then bv.one else bv.zero`, and all four compare instructions route
through it. The comparison itself was fine — `rs1_val <ᵘ rs2_val` is a
`RelVal bool` via `liftBinOp` — but feeding it to `if:` produced a
`formula_relop bvult` path condition, hence `secLeak` **goals** on *both*
comparison operands. Net effect: the verifier rejected the single most common
constant-time idiom there is (BearSSL's `EQ`/`NEQ`/`GT`; clang's
`seqz`/`snez`/`sltu`) on a branch-free ALU instruction. It went unnoticed for
years because no CFGVer example had ever used an `SLT*`.

**Diagnostic question when you hit a wall inside the ISA semantics:** is this
branch *making a decision*, or merely *materialising a value*? If both arms only
produce a constant, touch no memory, don't move the pc, and emit no leak event,
it is a modelling artifact.

**The fix is to express it as a pure operation, not to weaken the wall.** For
bool → 1-bit vector the primitive already exists: `bop.bvcons`
(`BinOps.v:83`) is `BinOp bool (bvec m) (bvec (S m))`, and at `m = 0` it *is*
the conversion — `bv.cons true bv.nil = bv.one`, `bv.cons false bv.nil =
bv.zero`, both by `reflexivity` (exhaustive: `bool` has two inhabitants;
`Bitvector.v:375/377`). Because `bop.evalRel = liftBinOp (eval op)`
(`BinOps.v:411`), the two-world reading is componentwise for free: a
`NonSyncVal true false` bit becomes `NonSyncVal bv.one bv.zero`, a value that
differs between worlds and is never observed. This is rule 2 below with a real
precedent. Nothing is needed in the Semantics — `Expressions.v:138/159`
dispatch generically through `uop.eval`/`uop.evalRel`.

**Why this is a faithfulness fix, not a soundness hole.** The leakage model
already treats ALU work as unobservable: `LeakEvent := LeakPc | LeakMemRead |
LeakMemWrite` (`case_study/RiscvPmp/Base.v:329`), and `bool_to_bits` emits none
of them in either version. So the blanket "secret-dependent control flow is
fatal" rule is a sound but **incomplete** over-approximation of the intended
leakage model, and the old `if:` was already inconsistent with it. The full
disclaimer for that model change is above `fun_bool_to_bits` in `Machine.v`.

### Do NOT weaken `formula_relop` to fix this

The tempting shortcut is to change `formula_relop`'s `NonSyncVal` case from
`False` to `p1 /\ p2` — the pairwise "holds in each world separately" reading,
which `formula_relop_op_move_projs` (`Formulas.v:170`) already characterises.
**Unsound on its own.** A symbolic path corresponds to a *pair* of runs: the
`then` path would cover pairs where both worlds satisfy the comparison and the
`else` path pairs where neither does, leaving pairs whose worlds **disagree**
covered by no path at all — while the executor still claims exhaustive demonic
coverage.

The sound general version is to split at a `NonSyncVal` bool into all four
world-pair cases (TT/TF/FT/FF) and require the *mixed* ones to be
observationally equal: `bool_to_bits`' mixed cases differ in value but make no
observation (fine), whereas a real branch differs in pc sequence (still caught).
That would retire this escape hatch for the whole class rather than
per-instruction. Open — see `TODOS.txt`.

### The wall cuts BOTH ways: a SyncVal-always-true relop ≡ `secLeak`

Corollary of the same `NonSyncVal ⇒ False` semantics, and the sound way to
simplify such a formula. If a relop is *unconditionally true whenever its
operands are public*, then as a `Formula` it is **exactly equivalent to
`secLeak`** of the operand — not to `formula_true`:

| operand | the relop | `secLeak` |
|---|---|---|
| `SyncVal v` | True (the arithmetic fact) | True |
| `NonSyncVal a b` | **False** (this wall) | **False** |

So `formula_relop` may be rewritten to `formula_secLeak`, which the ordinary
`assumption_formula` machinery then discharges against an assumed `secLeak t`.
Rewriting to `formula_true` instead is **unsound** — it silently drops the
publicness requirement.

Worked instance (`Symbolic/Solver.v`, `peval_formula_le'`, 2026-07-28):
`0 <= unsigned t` is *not* `formula_true`, because `unsigned` on a
`NonSyncVal` sends the relop to `False`; it *is* `formula_secLeak t`
(`secLeak_iff_unsigned_nonneg`). An earlier attempt had tried `formula_true`,
failed to prove it, and left the case as `default` with the proof commented
out — the `secLeak` form is what makes it go through. Discovering this by
hand cost a session; the pre-existing hand lemma `relval_fetch_lower`
(`CFGVer/Contracts.v`), which takes `secLeak X` as an explicit hypothesis, was
already evidence that the bound needs publicness.

**Practical test** before rewriting any relop over possibly-secret operands:
ask what it means on `NonSyncVal`. If the answer is "False, because of this
wall", the target is `secLeak`, never `True`.

## Practical rules for term-rewrite / peval / solver work on secret data

1. **Prefer pure-`bv` arithmetic canonical forms.** A form built only from
   `bvand/bvor/bvxor/shiftr/bvadd/bvsub/bvcons` never produces a `bool`, so it is
   *structurally immune* to the `NonSyncVal ⇒ False` trap. (This is why the
   mask-folding work chose all-`bv` forms and avoided `relop` entirely. That work
   was abandoned and reverted on 2026-07-21 and its plan doc
   `CFGVer/PLAN-solver-fold.md` no longer exists — recoverable from git history
   if ever needed; the reasoning survives in the `key_schedule_loop` scaling
   notes.)
2. **If you must introduce `relop`/`term_eq`** on data that can be secret, keep it a
   value sub-term (e.g. an argument to `bvcons`) and guarantee no rule ever lifts it
   into a `formula_bool` / `formula_relop` / `secLeak` position. On secret operands
   the whole point is that it stays symbolic and is never decided.
3. **Solver caveat:** the solver already special-cases `term_eq (term_val v) t` under
   a `SyncVal true` assumption (`Solver.v:1028`) — eq-terms have sync-context
   handling elsewhere, so a fresh value-level eq-term can be grabbed by rules that
   assume it is (or will become) synced. Another reason to stay in pure `bv` form.

> Note: this wall governs anything that becomes a *formula*. A rewrite whose two
> sides are both **pure terms** is a different regime — it is auto-sound over
> secrets with no case analysis (see **`relval-rewrite-over-secrets`**).
