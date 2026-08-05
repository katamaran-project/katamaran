# Adding a `peval` rule — the mask algebra and `bop.coalesce`

Concrete worked material for `theories/Symbolic/PartialEvaluation.v`. Read it
before adding a `peval` case, and especially before adding a new `BinOp`/`UnOp`.
Everything here is verified against the code, not recalled.

## Why these rules exist

Constant-time C turns a predicate into a full-word 0/~0 mask and ANDs it into an
expression instead of branching. That is *good* for us — a branch on secret data
hits the `NonSyncVal ⇒ False` wall (**secret-data-walls**) — but the raw
arithmetic spelling is verbose and, in one case, exponential.

Two ops carry the canonical forms:

| op | eval | spelling it replaces |
|---|---|---|
| `uop.expand : UnOp bool (bvec n)` | `if b then ones else zero` | `<compare>; addi -1` (`[b] - 1 = -[¬b]`) |
| `bop.coalesce {n} : BinOp (bvec n) (bvec n) (bvec n)` | `if bv.eqb x zero then y else x` | `x \| (-[x = 0] & y)` |

`uop.expand` takes the **predicate**, not a bitvector. That is deliberate: every
clang spelling of a predicate (`snez` = `sltu rd,x0,rs`, `seqz` = `sltiu rd,rs,1`,
any comparison) folds through one rule, and no width relation between the
compared operands and the mask has to be decided.

The five landed rules, all in `PartialEvaluation.v`:

1. `peval_bvadd_mask` — recognizes `ones ⊕ zext (bvcons b w)` (`bin w = 0`) → `expand (not b)`
2. `peval_bvnot` — `bvnot (expand b)` → `expand (not b)`
3. `peval_bvand_mask` / `peval_bvor_mask` — `expand b ∧/∨ expand b'` → `expand (b &&/|| b')`
4. `peval_bvxor_mask` — `expand b ⊕ expand b'` → `expand (b ≠ b')`
5. `peval_bvor_mask`'s coalesce branch — see below

## Why `coalesce` is an op and not sharing

`c |= -EQ0(c) & CMP(k[u], N[u])` (BearSSL `check_scalar`) mentions `c` **twice**,
so the accumulator satisfies `T(k+1) = or(and(mask(T k), CMP), T k)`, i.e.
`count(k+1) = 2·count(k) + 1` — `2^N − 1` nodes. At P-256's mandated N = 32 that
is ~4.3e9.

`coalesce C S` mentions `C` **once**: the zero test lives inside the op's eval
rather than as a second subterm. Measured on the real `check_scalar_instrs`
unrolled 1–4× (`Example/ZZCsUnroll.v` + `ZZCsRun1..4.v`):

| copies | `uop.expand` | `bop.coalesce` | `srl/sra by 31` |
|---|---|---|---|
| before | 1, 3, (7, 15) | — | 2, 6, (14, 30) |
| after | 0, 0, 0, 0 | 1, 2, 3, 4 | 2, 4, 6, 8 |

Physical sharing (a Gallina `let`, hash-consing) does **not** substitute for
this: it saves memory, not traversal — `peval`/`Term_eqb` still walk the
structure. What is needed is *opacity*, and an op provides it by fiat
(`PLAN-term-sharing.md`).

## Soundness is a plain `bv` identity

Both sides of any of these rules are pure terms, so the relational obligation
follows from the `Val`-level one by homomorphism of `inst`/`liftBinOp` — it
covers `NonSyncVal` (secret) inputs with **no two-world case split**
(**relval-rewrite-over-secrets**). `SyncVal`/`NonSyncVal` appear in the proofs
only because `cbn` exposes `liftBinOp`; never in a statement.

The `bv` facts live in `Bitvector.v`'s `Section Logical`, *after* `land`/`lor`'s
own lemmas: `land_if_ones`, `lor_if_ones`, `lxor_if_ones`, `not_if_ones`,
`uleb_zero`, `coalesce_mask` (+ `_andr`/`_orl`/`_orl_andr`).

## Traps

- **A rule that never fires is invisible.** Everything compiles; nothing
  happens. Dump a real VC to confirm firing, and add `reflexivity` self-tests
  (`grep "Lemma selftest_"` — 19 exist).
- **A `reflexivity` self-test needs CONCRETE operands** wherever the rule
  consults `Term_eqb` or a matcher: neither can reduce on an opaque term
  variable. The coalesce self-tests therefore use `term_val`s and pin the
  *pattern* only; that the rule fires on a real `term_var`-headed VC is what
  `ZZCsRun1.v` measures.
- **`peval` is bottom-up.** A node you *construct* inside a rule is never
  revisited by another rule in the same pass. `peval_bvadd_mask` emits
  `expand (not b)`, not `bvnot (expand b)`, for exactly this reason.
- **`peval_not` negates the relop rather than leaving a `not`.**
  `term_relop_neg bop.bvult = Basics.flip term_bvule` (`Terms.v:148`), so
  `¬(0 <ᵘ C)` arrives as **`C ≤ᵘ 0` — operands flipped, op changed**. Any
  pattern over a negated comparison must expect the positive form.
- **`cbn` reduces `bop.eval_relop_val` away** for a concrete relop. Use
  `cbn - [bop.eval_relop_val]` to keep the shape a bridging lemma matches
  (`eval_relop_neq_bool`, `eval_relop_bvule_zero`).
- **Match commuted operand orders.** `bvand`/`bvor` are commutative and nothing
  in `peval` normalizes their arguments — `peval_bvor_mask` falls through to
  `peval_binop'`, which only folds two values. The coalesce recognizer accepts
  all four orders, which is why `coalesce_mask` has three commuted corollaries.
- **Inversion lemmas must return the linking equation.** A `generalize`-style
  matcher discards it and leaves the `Some` branch unprovable as posed
  (`PLAN-ksl64.md` §2). Use a one-clause `Equations` matcher + `funelim`, as
  `bvmask_try_expand` / `bvand_split` do.
- **You cannot iterate these proofs interactively.** `PartialEvaluation.v` is
  inside a module functor and `rocq_start` replays vos-style, so position mode
  returns no goals mid-proof. Develop the pure `bv` lemmas in **preamble mode**
  at ~30 ms/attempt (`From Coq Require Import NArith Lia. From Katamaran Require
  Import Prelude Bitvector.` — `%N` needs `NArith`), then pay one compile.

## Adding a new `BinOp`: the plumbing sites

Adding a constructor to `bop.BinOp` touches five files. Append new bvec ops to
the **end** of `Term_bvec_case`/`Term_bvec_rect`'s hypothesis list, never
mid-list: the four positional callers then only grow at their tail. Each labels
its slots with `(*opname*)` comments — find them with `grep -n "(\*bvtake\*)"`.

| file | what |
|---|---|
| `Syntax/BinOps.v` | constructor; one `binoptel_eq_dec` clause; one `eval` clause |
| `Syntax/Terms.v` | optional `term_<op>` notation; a hypothesis + clause in `Term_bvec_case`; a hypothesis + positional arg in `Term_bvec_rect` |
| `Symbolic/Solver.v` | `simplify_eq_binop_val` + `simplify_eq_binop` clauses (`simplify_eq_binop_default*` for an opaque op); the two `Term_bvec_case` positional lists |
| `Symbolic/PartialEvaluation.v` | the two positional lists (`peval_bvdrop_eq`, `peval_bvtake_eq`); the rule; wiring in `peval_binop`; soundness |
| `Bitvector.v` | the `Val`-level identity the rule is proved from |

Arity of a positional slot = the hypothesis's own arguments **plus** whatever the
motive adds. For a `bvec`-`bvec`-`bvec` binop that is 3 in `Solver.v`'s
`simplify_eq_binop_bvapp'`/`bvcons'` (`n t1 t2`, with `default` still expecting
the equation) but 4 in `PartialEvaluation.v`'s `peval_bvdrop_eq`/`bvtake_eq`
(`n t1 t2 e`). Getting this wrong is a type error, not a silent bug.

Sites that do **not** need touching, verified by grep: nothing in
`case_study/` enumerates `BinOp`, and `Propositions.v`/`Worlds.v`/`Expressions.v`
mention individual binops only in notations. `Solver.v`'s big
`destruct op; cbn; auto` soundness proofs absorb a new *opaque* constructor
without shifting a bullet, because the leading `auto` /
`try apply simplify_eq_binop_default_spec` closes its goal.

A new opaque constructor is a **solver completeness risk everywhere**, not just
at its own rule — run the full gate, not just the file you edited.
