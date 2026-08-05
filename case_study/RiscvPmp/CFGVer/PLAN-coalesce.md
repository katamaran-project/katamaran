# PLAN-coalesce — collapse check_scalar's accumulator from 2^N to O(N)

Status: **NOT STARTED.** Everything it depends on has landed and is verified;
this document is the handoff. Branch `solver-expand-mask`, commits
`fcccba5e` → `42c73ee5`.

Read this first, then `secret-data-walls` and `relval-rewrite-over-secrets`
(both short). The `cfgver-executor` skill's "Backward-branch loops" banner is
the cost model referenced throughout.

---

## §1. The target, and why it is the only thing left blocking the exponent

BearSSL `check_scalar` (`ec_p256_m62.c:1610`, our `Example/BearSSLCheckScalar.v`)
has two loops. Loop 2 is the wall:

```c
for (u = 0; u < klen; u++)
    c |= -(int32_t)EQ0(c) & CMP(k[u], P256_N[u]);
```

`clang 18.1.3 --target=riscv32 -march=rv32i -O2` compiles the body to the 16
instructions in `check_scalar_instrs`. Its last four are the accumulator step:

```
snez a2, a0        (= sltu a2, x0, a0)   <-- read #1 of c
addi a2, a2, -1                          <-- a2 = mask(c == 0)
and  a1, a2, a1                          <-- mask & CMP
or   a0, a1, a0                          <-- read #2 of c
```

`c` occurs **twice**, so the register store's raw term doubles every trip.
Measured on the real instruction list (`Example/ZZCsUnroll.v`, committed):

| unrolled | `uop.expand` nodes | `srl/sra by 31` | printed VC | wall | RSS |
|---|---|---|---|---|---|
| 1 copy | 1 | 2 | 9,117 chars | 19.0 s | 3.17 GB |
| 2 copies | **3** | **6** | **44,099 chars** | 33.1 s | 3.61 GB |

Both counters triple, because

```
T(k+1) = or( and( mask(T k), CMP(k+1) ), T k )      -- T k appears TWICE
⟹ count(k+1) = 2·count(k) + 1  ⟹  2^N − 1
```

At the P-256-mandated **N = 32** that is ~4.3 × 10⁹ nodes. Note wall clock grew
only 1.74× against a 4.8× term — consistent with the cost law's finding that
term size is *not* the dominant driver at small N, which is exactly why this
looks harmless at N=2 and is fatal at N=32. Do not conclude from a cheap N=2
that the problem is mild.

`CMP(k[u], N[u])` uses its operands 4× each but they are **freshly loaded every
iteration**, so its ~20 nodes are a fixed per-iteration cost that never
compounds. Only `c`'s double use compounds. The wall is one instruction pair
wide.

---

## §2. What `coalesce` is

```
coalesce(x, y) = if x = 0 then y else x
               = x | ( -[x = 0] & y )      -- the spelling clang emits
```

Sticky "first nonzero wins": once `c` is nonzero it never changes again. With
`s_u := CMP(k[u], P256_N[u]) ∈ {0, 1, ~0}`, thirty-two applications give the
first differing byte's comparison, i.e. the sign of `k − P256_N` — the
constant-time lexicographic compare. Algebraically it is the **first-nonzero
monoid**: associative, unit `0`, and idempotent-once-nonzero.

Why it fixes the wall: `coalesce(C, S)` mentions `C` **once**, because the
zero-test is built into the op's semantics rather than appearing as a separate
subterm. So the accumulator becomes a chain of 32 nodes:

```
coalesce(coalesce(…coalesce(0, s₀)…, s₃₀), s₃₁)         -- O(N)
```

**Why an op and not sharing.** `PLAN-term-sharing.md` refuted representing the
duplication with Coq-level physical sharing (a Gallina `let`, hash-consing):
that saves *memory*, not *traversal* — `peval`/`Term_eqb` still walk the
structure. What is needed is **opacity**, and an op provides it by fiat.

---

## §3. The exact term to recognize — GROUND TRUTH, do not re-derive

Dumped from the executor, not inferred. `Example/ZZExpandDump.v` and
`Example/ZZCsUnroll.v` reproduce it; **re-dump before trusting any pattern**, as
a peval rule whose pattern never matches is invisible (it compiles, it just does
nothing).

After the mask rules that have landed, the accumulator step arrives as:

```coq
term_binop bop.bvor
  (term_binop bop.bvand
     (term_unop uop.expand
        (term_binop (bop.relop bop.bvule) C (term_val (ty.bvec 32) bv.zero)))
     S)
  C
```

Three things to note, each verified:

1. **The mask is ONE node over ONE POSITIVE relop.** `snez; addi -1` no longer
   arrives as a 5-node arithmetic chain, nor as `bvnot (expand …)`. `peval_not`
   negates the relop rather than leaving a `not`: `term_relop_neg bop.bvult =
   Basics.flip term_bvule` (`Terms.v:148`), so `¬(0 <ᵘ C)` becomes
   `C ≤ᵘ 0` — **operands flipped, op changed**. Pinned by
   `selftest_bvnot_expand_negates_relop`.
2. **`C ≤ᵘ 0` is the zero-test.** Unsigned, so `C ≤ᵘ 0 ⟺ C = 0`.
3. **Operand order** is `bvor (bvand MASK S) C` and `bvand MASK S` — from
   `and a1,a2,a1` / `or a0,a1,a0` under `RTYPE rs2 rs1 rd`. Nothing reorders
   them: `peval_bvor_mask` falls through to `peval_binop'`, which only folds two
   values. **Match both orders anyway** — `bvor`/`bvand` are commutative and a
   different compiler may emit them the other way.

---

## §4. Implementation

### 4.1 The op

```coq
bop.coalesce {n} : BinOp (bvec n) (bvec n) (bvec n)
eval x y := if bv.eqb x bv.zero then y else x
```

A **BinOp**, which is more plumbing than `uop.expand`'s UnOp was. Sites (find
the positional ones with `grep -n "(\*bvtake\*)"`):

| file | what |
|---|---|
| `Syntax/BinOps.v` | constructor; one `binoptel_eq_dec` clause; one `eval` clause (~line 401) |
| `Syntax/Terms.v` | a **binop** hypothesis in `Term_bvec_case` + its clause, and in `Term_bvec_rect` + its positional argument |
| `Symbolic/Solver.v` | opaque/default clauses beside `bop.bvand`/`bop.bvor` (~410/411, ~819/820); plus the two `Term_bvec_case` positional lists in `simplify_eq_binop_bvapp'` / `bvcons'` |
| `Symbolic/PartialEvaluation.v` | the two positional lists (`peval_bvdrop_eq`, `peval_bvtake_eq`); the recognizer; wiring; soundness |

### 4.2 The recognizer

Graft into the **`bop.bvor`** chain, after the rule-3 homomorphism attempt. No
conflict: rule 3 tries `bvmask_try_expand` on both operands, and operand 1 here
is a `bvand`, so it returns `None` and falls through. Suggested shape:

```
peval_bvor_mask t1 t2 :=
  both operands masks?      -> expand (b1 || b2)        (rule 3, landed)
  coalesce pattern of §3?   -> term_binop bop.coalesce C S
  otherwise                 -> peval_binop' bop.bvor t1 t2
```

**The one piece of real work: a width transport.** `Term_eqb` is *homogeneous* —
`Term_eqb [σ] (t1 t2 : Term Σ σ)` (`Terms.v:647`) — but the relop inside
`expand`'s predicate is at some width `k` that typing does not force to equal
the outer `n`. So comparing the inner `C` against the outer `C` needs
`Nat.eq_dec k n` + `eq_rect`. Precedent: the deleted `peval_bvxor_fold32`'s
width dispatch, recoverable with
`git show 027d7c27 -- theories/Symbolic/PartialEvaluation.v`.

Use `Equations` with `option`-wrapped matchers for the destructuring, and have
the inversion lemma **return the equation** linking the term to the recognized
shape — see §6.

### 4.3 Soundness

Pure-term rewrite on both sides, so by the homomorphism argument
(`relval-rewrite-over-secrets`) the obligation is a plain `bv` identity and
covers `NonSyncVal` (secret) inputs with **no two-world case split**. The
identity:

```
(if bv.eqb x bv.zero then y else x)
  = bv.lor (bv.land (if bv.uleb x bv.zero then bv.ones n else bv.zero) y) x
```

Two cases, both discharged from lemmas already in `Bitvector.v`:
`x = 0` → `land_ones_l`, `lor_zero_r`; `x ≠ 0` → `land_zero_l`, `lor_zero_l`.

**The one new `bv` fact needed:** `bv.uleb x bv.zero = bv.eqb x bv.zero` (or
`↔ bin x = 0`). Nothing in the library states it. Prove it next to the mask
algebra block in `Bitvector.v` (after `land`/`lor`'s own lemmas — placement
matters, see §6).

Plus: the recognizer's `Term_eqb` use needs `Term_eqb_spec` (`Terms.v:680`,
a `BoolSpec`; the idiom in this codebase is `destruct (Term_eqb_spec t1 t2);
subst`).

---

## §5. Acceptance criterion — measurable, with probes already committed

`Example/ZZCsUnroll.v` + `ZZCsRun1.v`/`ZZCsRun2.v` are the real
`check_scalar_instrs` unrolled 1× and 2×. Re-run them:

```
coqc -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
     case_study/RiscvPmp/CFGVer/Example/ZZCsRun2.v > out.txt
grep -o 'uop.expand' out.txt | wc -l ; grep -o '\[bv 0x1f\]' out.txt | wc -l
```

| | now (doubling) | with `coalesce` (linear) |
|---|---|---|
| `srl/sra by 31`, 1 copy | 2 | 2 |
| `srl/sra by 31`, 2 copies | **6** | **4** |
| `uop.expand`, 1 copy | 1 | **0** |
| `uop.expand`, 2 copies | 3 | **0** |

The `expand` count should drop to **zero**: the accumulator's mask is *absorbed
into* the `coalesce` node, and it was the only mask in the program. The shift
count going 2 → 4 rather than 2 → 6 is the linearity. If `expand` does not go to
zero, the recognizer is matching something other than §3's shape.

Then: `valid_check_scalar_cfg_contract_param` must still discharge on the
unchanged one-liner (`intros; vm_compute; solve_vc; solve_symbase_fetch`), and
the whole tree must stay green — `bop.coalesce` becomes a new opaque constructor
for the Solver, which is a completeness risk everywhere, not just here.

---

## §6. Traps that cost time this session — do not re-pay them

- **A peval rule that never fires is invisible.** Everything compiles; nothing
  happens. Always dump a real VC to confirm firing, and add `reflexivity`
  self-tests (13 exist, `grep "Lemma selftest_"` in `PartialEvaluation.v`).
- **`peval` is bottom-up.** A node you *construct* inside a rule is never
  revisited by another rule in the same pass. `peval_bvadd_mask` originally
  emitted `bvnot (expand b)` and `peval_bvnot` never saw it; it now emits
  `expand (not b)` directly. (The `not` still disappears — the mask is written
  to a register and re-`peval`'d when read back.)
- **Inversion lemmas must return the linking equation.** The deleted
  `select_last_k` fold used `generalize` on its matcher, which discards exactly
  that equation and leaves the `Some` branch unprovable as posed
  (`PLAN-ksl64.md` §2). Use `destruct … eqn:` + an explicit inversion lemma.
- **Lemma placement in `Bitvector.v`.** A new lemma placed before the `land`/
  `lor` lemmas it needs fails *indirectly*: the rewrites silently do not fire
  and `reflexivity` fails, rather than an unbound-name error. Put mask-algebra
  facts after the `Logical` section's own lemmas.
- **`cbn` reduces `bop.eval_relop_val` away** for a concrete relop. Use
  `cbn - [bop.eval_relop_val]` to keep the shape a bridging lemma matches.
- **`apply f_equal` mis-unifies against `SyncVal`'s dependent type;** the
  `f_equal` *tactic* works and distributes over the subgoals it creates. Val
  goals often come out in the opposite orientation to the lemma, so
  `now rewrite bv.X` is more robust than `apply bv.X`. The file's own
  `destructInsts` tactic (`Instantiation.v:83`) splits `RelVal`s.
- **`uop.expand`'s result width is not fixed by its bool argument** — needs
  `(n := n)` where context does not determine it.
- **Probe-file scope traps:** `++`/`::` are hijacked by `ctx.notations` (needs
  `Open Scope list_scope.`), and a probe that Requires only a helper file cannot
  see `Prelude`'s notations unless that helper uses `Require Export`.
- **Iteration cost.** `PartialEvaluation.v` is inside a module functor, and
  `rocq_start` replays vos-style (proof bodies skipped), so **position mode
  returns no goals mid-proof** — you cannot iterate these proofs interactively.
  Pure `bv` lemmas *can* be developed in preamble mode at ~30 ms/attempt
  (`From Coq Require Import NArith Lia. From Katamaran Require Import Prelude
  Bitvector.` — note `%N` needs `NArith` or numerals default to `nat`). Do that
  for §4.3's identity, then pay one ~90 s compile.
- **Build budget.** A `-j1` full tree takes ≳1 h here; 90 min is not enough
  (one run died on a `timeout`, which looks exactly like an OOM but is not).
  `-j2` wants ~7.2 GB against ~6.5 GB free with a desktop loaded, and
  `Cmovznz4` peaks at 5.7 GB.

---

## §7. Already refuted — do not retry

- **Havoc-the-secret** (2026-07-19).
- **Physical sharing / hash-consing** for this (`PLAN-term-sharing.md`): saves
  memory, not traversal.
- **Generic SSA value-naming at register writes.** The principled fix for the
  whole class, but it is a core redesign: the path condition would substitute
  the defining equation straight back in (that is what `unify_pathcondition` is
  *for*), it needs a non-substitutable binding class, correct variable polarity,
  and re-proving refinement/soundness. Explicitly ruled out of scope by the
  user; it belongs upstream with Dominique/Steven (already in `TODO.md`).
- **A ternary `select`.** There is no `term_ternop`, and adding one touches
  `subst`/`inst`/`occurs`/`Term_eqb`/`eq_dec`/every eliminator plus the
  refinement layer. Also would *not* fix this wall: `select(expand(0 <ᵘ c), s, c)`
  still mentions `c` twice.
- **Unrolling the loop.** Term growth is a property of the instruction
  sequence, not the loop encoding.

---

## §8. What `coalesce` will NOT fix

- **Driver 2, cells × steps.** `chunk_gc` filters only `is_encodes_instr`;
  declared *data* cells stay resident, and per-step cost is linear in heap size.
  Full loop 2 is ~416 steps against 64 array bytes. Reference point:
  `modpow_win_full` = 122 steps / ~12–16 cells at 63 s `vm_compute` + 38 s
  `Qed`. Lever: `P256_N` is a **public constant** array — pinned public values
  fold to literals and stay size-1, so declare those 32 cells `PVConst` and only
  `k`'s 32 bytes need to be existential.
- **Byte-granular memory.** `k[u]`/`P256_N[u]` are `lbu`. The machine model
  supports it (`fun_execute_LOAD` dispatches `BYTE → mem_read 1`), but
  `Tables.v`'s `LW`/`SW` helpers hardcode `WORD` and every example is
  word-granular, so whether `mem_full_spec` can declare byte cells is
  **unverified**. This gates both loops and is independent of `coalesce`.
- **Loop 1** (`z |= k[u]`) is *not* term-walled — `z` occurs once — but it is
  not growth-free either: linear, ~32 nodes at N=32. It is the cheap probe for
  driver 2 in isolation.

---

## §9. Other open items, none blocking

- **Reinstating `peval_bvand`/`peval_bvor`.** Their commented-out soundness
  proofs *look* complete but predate the `RelVal` migration — they rewrite
  `bv.land` under an un-split `RelVal` and fail with "found no subterm matching
  `bv.land ? zero`". Needs `destructInsts` threaded through and the
  `land_comm`/`orb_comm` cases restructured: six proofs, blind ~90 s compiles.
  Left byte-identical to how they were found. Would also unblock writing the
  `peval_bvxor` constant-propagation family on the same pattern.
- **Shift-based mask formation.** `srai x,31` *is* a mask (`-[msb x]`),
  `srli x,31` is the 0/1 bit — these are the two `GT` masks inside
  `check_scalar` that `expand` does not reach (visible as §5's `srl/sra by 31`
  counts). Tempting and **not worth it**: `CMP = GT(x,y) | -GT(y,x)` combines a
  0/1 value with a mask, not two masks, so no homomorphism rule fires and
  nothing collapses.
- **select/MUX canonicalization** (`y ^ (m & (a^b))` ↔ `(m&a) | (~m&b)`) — still
  open, unconditionally sound (the two spellings are equal *bitwise for every*
  `m`). Careful: clang's `c | (m & s)` is **not** a select — with `c=1, m=~0,
  s=0` the OR gives `1` but `select(~0,0,1) = 0`. It is only equal because the
  mask is derived from `c`, which is `coalesce`'s own side condition.
- **`bop.eq` at `σ = ty.bool` is xnor**, the twin of the `neq`-as-xor trick rule
  4 uses, if a use ever appears.

---

## §10. What has landed (all `Qed`, no admits, no new axioms)

| commit | contents |
|---|---|
| `fcccba5e` | `uop.expand : UnOp bool (bvec n)`, eval `if b then ones else zero` — Botan's `CT::Mask::expand`; recognizer in `peval_bvadd` for `<compare>; addi -1`; `bv.not_zero`, `bv.add_zext_cons_ones`, `bv.onesn_S`, `bv.onesn_exp2` |
| `83851b81` | rules 1–3 (`bvnot`/`bvand`/`bvor` homomorphism); `bv.land_if_ones`, `lor_if_ones`, `not_if_ones`; **first wiring of `bop.bvand`/`bop.bvor` into `peval_binop`** |
| `3a3a19ff` | rule 4 via `bop.relop bop.neq` at `σ = ty.bool`; the whole missing `bv.lxor` family + four `N_lxor_*` helpers |
| `84ef2ea7` | demo probes `ZZMaskAlgebra.v`, `ZZCsUnroll.v`, `ZZCsRun1/2.v` |
| `42c73ee5` | 13 `reflexivity` regression tests |

The op takes the **predicate**, not a bitvector: every clang spelling of a
predicate (`snez` = `sltu rd,x0,rs`, `seqz` = `sltiu rd,rs,1`, any comparison)
folds through one rule, and no width relation between the compared operands and
the mask has to be decided. The algebra is closed under `&`, `|`, `^`, `~`.

Verification status: `fcccba5e` and `83851b81` are full-tree green and
axiom-clean (`check_scalar`, `modpow_win_full`, `cmovznz4` `_param` theorems show
only the allowlisted `Machine.pure_decode` / `Base.mmioenv`). `3a3a19ff` and
`42c73ee5` are per-file green with a **full tree still running at the time of
writing** — confirm it before merging.
