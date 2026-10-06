---
name: leakage-model-change
description: Changing WHAT the RiscvPmp machine observes — adding, removing or re-typing a `LeakEvent` constructor and the `stm_foreign leak` sites that emit it. Use whenever the request is about making an instruction leak something it did not leak before (or stop leaking something), e.g. "make multiplication leak its operands", "model a variable-latency divider", "what if loads leaked the value and not just the address", "add a new leakage event", "does verification still work if X leaks" — and also when auditing or explaining which instructions are observable in this model. Covers the six mechanical edit sites in `Base.v`, the one-line emit discipline in `Machine.v` (the trusted Sail-derived surface, where the ONLY code delta may be the leak statement), and — the part most often gotten wrong — which proofs and contracts actually need re-proving, which is normally NONE, and the specific circumstances where that stops being true. NOT for why a VC over secret data collapses to False (`secret-data-walls`), NOT for discharging the resulting VC (`cfgver-solve-vc`), and NOT for verifying a new program under an UNCHANGED model (`cfgver-new-example`).
---

# Changing the leakage model

The leakage model is the answer to "what can the attacker see". Changing it
changes the *meaning* of every noninterference theorem in the tree at once,
which sounds alarming and is in fact cheap — but only if you change the right
six-plus-one places and nothing else. This skill is the map.

Worked example, with measurements and a refuted prediction:
`case_study/RiscvPmp/CFGVer/diagnostics/mul-leakage-model.md` (adding `LeakMul`,
2026-09-08). Read it if you want the evidence behind the claims here.

## 1. What the model is, in three definitions

```coq
Inductive LeakEvent : Set := …                      (* Base.v — the vocabulary  *)
Definition LeakageTrace := list LeakEvent.          (* Base.v                   *)
Definition fun_leak μ e := … (cons e (leakage_trace μ)).   (* Base.v — append   *)
```

and one statement, which is the whole point:

```coq
noninterferent_strong … :=                          (* CFGVer/Noninterference.v *)
  … → leakage_trace μ1' = leakage_trace μ2'
```

**The conclusion quantifies over `list LeakEvent` abstractly.** That single fact
explains almost everything below: adding a constructor *strengthens every
existing theorem in place*, without restating any of them, because there are
now strictly more observations that have to agree between the two worlds.
Nothing has to be re-derived because nothing named the constructors.

## 2. The exact edit sites

### `case_study/RiscvPmp/Base.v` — six arms, all mechanical

Grep the anchor, don't trust a line number (these drift).

| # | anchor | what to add |
|---|---|---|
| 1 | `Inductive LeakEvent : Set :=` | the constructor, e.g. `\| LeakMul : bv xlenbits -> bv xlenbits -> LeakEvent` |
| 2 | `Inductive LeakEventConstructor : Set :=` | the tag, `\| KLeakMul` |
| 3 | `LeakEventConstructor_finite` | add the tag to `enum := [ … ]` |
| 4 | `union_constructor_type`, `leak_event` arm | the payload **type** |
| 5 | `union_unfold`, `leak_event` arm | `\| LeakMul v1 v2 => existT KLeakMul (v1 , v2)` |
| 6 | `union_fold`, `leak_event` arm | `\| existT KLeakMul (v1 , v2) => LeakMul v1 v2` |

Miss one of 3–6 and you get a non-exhaustive-match or `Finite` error at
`Base.v` — loud and immediate, so this list is self-checking. The `typedefkit`
obligations underneath (`unionv_fold_unfold` / `unionv_unfold_fold`) are
discharged by an `abstract (intros [] [[] x]; repeat destruct unit/prod; auto)`
that already handles `unit`, `prod` and tuple payloads, so they normally need
no attention.

**Payload typing — the one real choice.** For a multi-value event prefer
`ty.prod` built with `exp_binop bop.pair` over `ty.tuple`:

- `simplify_secLeak` (`theories/Symbolic/Solver.v`) splits `term_binop` into
  both operands (`cat`), so a `prod` payload yields one `secLeak` obligation
  **per value**, each matchable against the per-variable facts a public
  `reg_spec` puts in `wco`.
- Its `term_tuple` and `term_record` arms are `dlist_secLeak t` with a standing
  `TODO` — no structural split — so a tuple payload gives you one atomic
  obligation that nothing can discharge.

Its `term_union` arm also does not recurse, which *looks* like it breaks the
`prod` case too. It does not: `combined_solver` runs `solver_generic` several
times, so a later pass re-simplifies the payload. This was predicted to require
a `Solver.v` fix and the prediction was **wrong** — check before building
machinery, the check is a 4-line probe and the "fix" is a ~6 min `Solver.vo`
rebuild plus full downstream `.vo` invalidation.

### `case_study/RiscvPmp/Machine.v` — the emit sites

`grep -n "stm_foreign leak" case_study/RiscvPmp/Machine.v` lists the complete
set; today that is the pc in `fun_fetch`, the address in
`fun_checked_mem_read` / `fun_checked_mem_write`, and the operands in
`fun_execute_MUL`. An emit is one statement:

```coq
stm_foreign leak [exp_union leak_event KLeakMul
                    (exp_binop bop.pair rs1_val rs2_val)];;
```

Three placement rules, each with a reason:

- **After the values are bound, before they are used.** Then the event carries
  the raw values and is unaffected by whatever the instruction does with them
  (sign extension, word selection). Put it earlier and you are leaking
  something the instruction has not read yet.
- **Sequenced with `;;`, never bound with `let:`.** `stm_foreign leak` returns
  `unit`. Sequencing leaves the instruction's value flow bit-for-bit identical,
  so the only difference in a concrete run is one extra `cons` on the trace.
  This is what makes the change auditable.
- **One emit covers a whole instruction family if they share a body.** All of
  `MUL`/`MULH`/`MULHU`/`MULHSU` dispatch to `fun_execute_MUL`; its
  `high`/`signed1`/`signed2` flags only change how the product is *read*. Check
  the dispatcher (`fun_execute`) before adding a second emit you don't need.

## 3. Change ONLY leak statements

`Machine.v` and `Base.v` are the trusted machine model. A reviewer has to be
able to confirm, from the diff alone, that machine *behaviour* is unchanged and
only the trace grew. That is impossible if the diff also contains a rename, a
tidy-up, or a "while I'm here" fix.

So in the same commit, the code delta must be exactly the `stm_foreign leak`
statements plus the six `Base.v` arms. Concretely:

- Do not touch the instruction's value computation, not even to make it
  clearer.
- Do not reorder existing statements.
- Do not fix an unrelated bug you spot in the same function. Separate commit.
- Comments are the exception and are usually *obligatory* — see below.

**Check yourself with the diff, not from memory:**

```bash
git diff <base>..HEAD -- case_study/RiscvPmp/Machine.v \
  | grep '^[-+]' | grep -v '^[-+][-+]'
```

Every `+` line should be a leak statement or a comment. If a `-` line appears
outside a comment block, you changed behaviour — justify it or split it out.

**Comments that must be repaired.** Prose elsewhere in `Machine.v` states the
model's shape and gets silently falsified. The note above `fun_bool_to_bits`
enumerates `LeakEvent`'s constructors, counts the emit sites, and argues from
"ALU operations are unobservable" — all three break when you add an arithmetic
event. Grep for stale claims before committing:

```bash
grep -n "LeakEvent :=\|LeakPc\|three sites\|four sites" case_study/RiscvPmp/Machine.v
```

Fixing a comment is not scope creep here; leaving a false statement in the
trusted surface is worse than the edit.

## 4. What needs re-proving: normally nothing

This is the part people over-estimate. Adding a constructor and an emit site
needed **zero** changes in `theories/`, in the CFGVer light or heavy branch, or
in any of the 18 pre-existing end theorems. Three structural reasons, each
worth checking still holds for your change:

1. **The leak contract is generic in the event.** `sep_contract_leak`
   (`CFGVer/Spec.v`, and a twin in `Contracts.v`) has precondition
   `asn_inv_leakage ∗ secLeakvar "leak"` — publicness of *whatever the event
   carries*, with no per-constructor case.
2. **Its soundness proof never destructs the event.** `leak_sound`
   (`CFGVer/SpecIris.v`, twin at `ModelBinary.v`) is the single lemma tying
   that contract to `ForeignCall leak [le] … = (γ, fun_leak μ le, inr tt)`. It
   keeps the event abstract and discharges the precondition with
   `secLeakOtherDef : secLeak rv <-> rv = SyncVal (ty.projLeft rv)` — "the
   event is literally the same value in both worlds" — after which both
   worlds' `cons e t` updates are syntactically identical.
3. **Arithmetic instructions have no contract to update.** `CEnv` (`CFGVer/Spec.v`)
   returns `Some` for `rX`, `wX`, `fetch`, `mem_read`, `mem_write_value`,
   `tick_pc`, `within_phys_mem`, `checked_mem_read/write` and `execute_EBREAK`,
   and `None` for everything else — so `execute_MUL` and friends are **inlined**
   (`sexec_call`, `SymbolicExecutor.v`; CFGVer runs `FunDef step` at
   `inline_fuel := 10`, `CFGVer/Verifier.v`).

### When that stops being true

- **The instruction you are instrumenting HAS a contract in `CEnv`.** Then the
  leak is behind a contract boundary: add the publicness requirement
  (`secLeakvar` on each leaked value) to that contract's precondition *and*
  re-prove its `ValidContract`, and expect every caller's obligations to shift.
  `checked_mem_read`/`checked_mem_write` are in this category — the two
  existing memory emits already live inside contracted functions.
- **You add a new KIND of side condition.** Everything here rests on
  publicness being a property of one `RelVal`. A model needing a *relation*
  between two events, an ordering constraint, or a count would not inherit
  `leak_sound` and is a genuinely different piece of work.
- **You REMOVE a constructor.** Deleting the emit weakens every theorem, so
  "it still compiles" proves nothing at all. Removal needs an argument that the
  observation was never real, not a green build.

### Cost, not correctness

Because the instruction is inlined, the obligation is re-derived at **every
occurrence** in the unrolled trace rather than once at a contract boundary.
Free on a short program, a real per-instruction cost in a loop that leaks on
every trip. Putting the instruction behind a contract trades that for the
re-proving work above.

## 5. Verify it with three cells, not one

A green build is not evidence. Adding a constructor without reaching the emit
leaves every theorem exactly as strong as before, and looks identical to
success. Hold the program, base, fuel and tactic line fixed and move one axis:

| cell | expectation |
|---|---|
| leaked values all **public** | VC discharges |
| one leaked value **secret** | fails, on exactly `secLeak` of that value |
| same secret program, **emit line commented out** | discharges again |

The third cell is the load-bearing one, and is the cell people skip. Without
it, the second cell's failure is equally consistent with some unrelated wall in
the instruction body (a `uop.signed` on a `NonSyncVal`, a widening, a subrange)
— see `secret-data-walls`. With it, the whole gap is attributable to your event.
It costs one light-chain rebuild (~2 min): comment out the emit, rebuild to
`Example/Prelude.vo`, re-run the secret probe, restore.

Read the residual rather than just observing failure — it should name the
secret value and show the public ones already discharged:

```
H0 : … (eformula_secLeak (eterm_var "v.1"))   (* public — available *)
|-   … (eformula_secLeak (eterm_var "v"))     (* secret — open      *)
```

Probes go in `Example/ZZ*.v`, which `.gitignore` already excludes.

Then the real regression: `GATE_JOBS=1 ./scripts/gate.sh`. Pre-existing
theorems re-passing is a genuine result (§1), though note what it does and does
not show — if none of them uses the instrumented instruction, it shows the
extension is *conservative*, not that anything new was discharged.

## 6. What is never proved

That the model matches hardware. Nothing in Coq says a real multiplier leaks
exactly its two operands and nothing else, or that `slt`/`sltu` leak nothing.
These are assumptions, and because they are structural they do **not** appear
in `Print Assumptions` — the end theorems still read as axiom-clean.

State this when reporting. The honest form is "constant-time *relative to a
model in which …*", and the model's faithfulness is the reader's to accept.

## 7. Build order

`Base.v` invalidates the whole case study; `theories/` is untouched, so nothing
heavy rebuilds.

```bash
make -f Makefile.coq case_study/RiscvPmp/Base.vo                       # ~40 s
make -f Makefile.coq case_study/RiscvPmp/Machine.vo                    # ~15 s
make -f Makefile.coq case_study/RiscvPmp/CFGVer/Example/Prelude.vo     # ~2 min, light chain
make -f Makefile.coq case_study/RiscvPmp/CFGVer/EndToEnd.vo            # ~8 min, heavy chain
GATE_JOBS=1 ./scripts/gate.sh
```

Two traps, both of which have cost time here:

- `rocq_compile_file` on a `CFGVer/Example/*.v` compiles into `_build/default`,
  **not** the source tree, so a later `Require` of it fails confusingly. Use
  `make` for anything a sibling needs.
- A rebuilt `.vo` is invisible to a live `rocq_start` session until
  `force_restart=True`. Symptom: `Locate` reports a name that is definitely in
  the freshly built file as absent.
