# PLAN — `nextpc` as a contract parameter (kill the per-step demonic variable)

Status: in progress. Written 2026-07-31.
Branch `nextpc-param`, based on **`30c9517a`** — deliberately NOT on the GC line.

## Provenance: why this branch starts where it does

The world-GC/chunk-GC work is archived at the tag **`archive/gc-attempt-2026-07`**
(tip `48c651f0`, branch `unquantify-gate`). Read `git tag -n99
archive/gc-attempt-2026-07` for what is recoverable from it and how.

`30c9517a` is the last commit where:

| | |
|---|---|
| `Admitted` in `VerifierRel.v` | **0** — `rexec_cfg_addr` is a real, compiling proof |
| binds per step in `sexec_cfg_addr` | **1**, matching the concrete side exactly |
| GC machinery | absent; `CFG_VC_triple` has no `gc`/`wgc` parameters |

So this change threads one extra argument through a *working* proof, rather
than reconstructing a proof from a comment and closing an admit.

Note the history already reset to this same commit once: `9b6fbab4`'s message
records that the earlier `rexec_cfg_addr` attempts (`0015f040`, `9d59b291`)
stated bind-pairing **axioms** and derived the refinement from them, i.e.
assumed the result. §0 explains why they had to.

---

## §0. Why the world-GC could not be saved (keep this; it is the expensive lesson)

`gc_dead_roots` pinned a forward-dead logical variable `x` to an arbitrary
inhabitant and emitted `assume_triangular ν`, i.e. *"if `x = v`, then «rest»"*.
That is sound at the top of the tree, where `x` sits under a ∀ (the enclosing
`demonicv`) and «rest» does not mention `x`. It is **not** provable as a local
refinement lemma, because a refinement lemma is stated at one FIXED valuation
and no longer sees that ∀: at a valuation with `x ≠ v` the premise is vacuously
true, so the lemma must conclude something real from nothing.

The obstruction is structural, not a matter of choosing a better `v`:

- A world change is carried by a `Sub`, which must say what **every** variable
  becomes, including the one being removed. There is no term over the smaller
  context meaning "whatever `x` was", so deleting forces committing.
- Committing to `x = v` narrows the valuation map
  (`inst (sub_single xIn (term_val v))` is not surjective), and `RBox`'s
  `assuming` (`UnifLogic.v:1406`, `Worlds.v:755`) transports the continuation's
  correctness only along that map. Valuations outside the image yield nothing —
  from the tree *or* from the continuation hypothesis.
- The alternative, a genuine deletion whose valuation map is the total,
  surjective "forget `x`", corresponds to a `Sub (wctx w - x) (wctx w)`, i.e. a
  move **backwards** in the world order. `RBox` quantifies only over future
  worlds, so the continuation's relation is unavailable there too.

Contrast the solver, which shrinks the world constantly and whose refinement
proof works (`refine_assume_pathcondition`, `Refinement/Monads.v:345`): there
the substituted equation *follows from the path condition at the current
valuation*, so no valuation is uncovered — that is what
`inst_triangular_knowing` (`Propositions.v:2409`) provides and what an
arbitrary pin cannot have. The framework's own `solve_uvars` makes the same
point from the other side: `uctx_subst` (`Propositions.v:1556`) refuses
(`isCatLeft → None`) exactly when the variable lives in the ambient context
rather than a locally-quantified suffix, because only then is the ∀ in hand.

Sharpest form: `is_dead` required `x ∉ wco w`, so **the very condition that
justified the GC semantically is what guaranteed the bad valuations exist.**

**Therefore: attack the growth, not the shrinkage.**

---

## §1. What this plan buys, and what it does not

Two demonic variables per step were introduced and never eliminated (measured;
see the `project-key-schedule-loop-scaling` memory note):

| variable | source | after this plan |
|---|---|---|
| `an` | `exec_instruction_prologue` (`Verifier.v:126`) | **gone** — one variable total, not one per step |
| `encoded_instr` | `sep_contract_fetch_instr` postcondition (`Spec.v:311`) | **untouched** |

So `|wctx|` still grows linearly, at half the previous rate. Against the note's
measured `|wctx| ×1.97 → 2.19× cost` this should be a substantial win, but the
factor is **not predictable from that one datapoint** — measure it (§5), do not
quote a number in advance. This does **not** on its own reach the 10.59× the
(unsound) world-GC appeared to deliver.

---

## §2. The idea: a ∀-parameter is not an assumption

The prologue existentially quantified the incoming `nextpc` value, and because
the prologue is **produced** (`VerifierRel.v:115` — `produce`, not `consume`)
that existential became a fresh *demonic* variable every step.

These two contracts are the same statement:

    { ∃ n. pc ↦ a ∗ nextpc ↦ n ∗ … }  step  { … }        (before)
    ∀ n. { pc ↦ a ∗ nextpc ↦ n ∗ … }  step  { … }        (this plan)

A ∀-parameter is exactly as general as an existential, so the contract stays
self-contained and covers any incoming `nextpc`. **This is not the same as
assuming `nextpc = pc`**, which would be a genuine strengthening and was
rejected on exactly those grounds. Only what the executor does changes: instead
of minting a fresh variable it supplies a term it already holds.

Which term? After a step the epilogue gives `pc ↦ an ∗ nextpc ↦ an` — the same
`an` — so from step two onward the incoming value is just `apc'`. Only the
**first** step genuinely does not know it, so one demonic variable is introduced
once, before the loop.

Why the value cannot matter to behaviour (checked): `fun_step`
(`Machine.v:885`) does `stm_write_register nextpc (pc +ᵇ 4)` *before*
`call execute`, so the incoming value is overwritten before any read. It **is**
read later — `execute_RISCV_JAL`/`JALR` for the link register
(`Machine.v:1235`, `1243`) and `tick_pc` (`Machine.v:640`) — but always after
that write.

---

## §3. The changes, file by file

### 3a. `Verifier.v` — the prologue (epilogue unchanged)

Context gains `"np"`; the existential becomes a plain chunk:

```coq
Definition exec_instruction_prologue (i : AST) :
  Assertion ([ctx] ▻ ("a":: ty_xlenbits) ▻ ("np":: ty_xlenbits)) :=
  pc     ↦ term_var "a" ∗
  asn.chunk (chunk_user ptstoinstr [term_var "a"; term_val ty_ast i]) ∗
  nextpc ↦ term_var "np" ∗
  asn.formula (formula_secLeak (term_var "a")).
```

`exec_instruction_epilogue` is **unchanged** — it keeps `nextpc ↦ term_var "an"`.
That is the postcondition, it is genuinely true, and it is what tells the caller
the new value. Keeping the consume/produce round-trip is what preserves
modularity: the per-instruction frame still describes its own footprint. The
chunk's value round-trips identically, so heap content is unchanged; only the
fresh variable disappears.

### 3b. `Verifier.v` — `sexec_instruction`

Extra argument, threaded into the produce environment:

```coq
Definition sexec_instruction (i : AST) :
  ⊢ STerm ty_xlenbits -> STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
  fun _ a np =>
    ⟨ θ1 ⟩ _ <- produce (exec_instruction_prologue i)
                  [env].["a"∷_ ↦ a].["np"∷_ ↦ np] ;;
    (* θ2, θ3, θ4 and the epilogue consume: unchanged *)
```

### 3c. `Verifier.v` — `sexec_cfg_addr`

Still ONE bind per step on this base. Add the `nextpc` argument; in the
recursive call it and the pc are the same term `apc'`:

```coq
Fixpoint sexec_cfg_addr (fuel : nat) :
  ⊢ SInstrTable -> SExitTable -> STerm ty_xlenbits -> STerm ty_xlenbits ->
    SHeapSpec (STerm ty_xlenbits) :=
  fun w tbl exits apc anp =>
    …
    | Some i =>
        ⟨ θ1 ⟩ apc' <- sexec_instruction i apc anp ;;
        sexec_cfg_addr n' (persist_itable θ1 tbl) (persist_etable θ1 exits)
          apc' apc'
    end
```

### 3d. `Verifier.v` — `sexec_triple_addr`: the one new variable

```coq
⟨ θ0 ⟩ δ  <- demonic_ctx id Σ ;;
⟨ θ1 ⟩ a  <- demonic (Some "a") _ ;;
⟨ θ1'⟩ np <- demonic (Some "np") _ ;;          (* NEW — once, not per step *)
…
⟨ θ3 ⟩ na <- sexec_cfg_addr fuel (subst_itable ζ tbl) (subst_etable ζ exits)
                a2 (persist__term np θ2) ;;
```

`δ1`, `a2` and `ζ` each gain `θ1'` in their persist chains. This adds one
top-level demonic binder to every example's VC — constant, not per-step.

### 3e. `VerifierRel.v` — the concrete mirror

`cexec_instruction` (line 111) and `cexec_cfg_addr` (line 125) take the extra
argument and thread it identically; the recursive call passes `apc' apc'`.
`mono_cexec_instruction` (147) and `mono_cexec_cfg_addr` (151) need the added
parameter in their statements. `cexec_triple_addr` (466) gains a
`CHeapSpec.demonic` mirroring §3d.

### 3f. `VerifierRel.v` — `rexec_instruction` (190) and `rexec_cfg_addr` (383)

`rexec_instruction` is a bare `rsolve`; it gains one arrow:

```coq
⊢ ℛ⟦RVal ty_xlenbits -> RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits)⟧
    (cexec_instruction i) (sexec_instruction (w := w) i)
```

Expect it to stay one `rsolve` and get slightly *cheaper*: one fewer
`demonic`/`refine_demonic` pairing, replaced by an environment entry discharged
from the new `ℛ⟦RVal ty_xlenbits⟧ npc snpc` hypothesis. Update
`refine_compat_exec_instruction` for the new arity.

`rexec_cfg_addr` is a **real proof on this base** — extend it, do not re-derive.
The `iInduction fuel` and the four `is_exit`/`lookup_instr` cases are unchanged;
the boxed IH now has to carry the extra argument.

### 3g. `VerifierRel.v` — `sound_exec_instruction` (676)

`semTripleOneInstrStep` (671) currently takes the `∃` in its precondition and
the proof instantiates the executor's ∀ from it:

```coq
(* PRE has (∃ v, lptsreg nextpc v); the proof does *)
iIntros (Hverif) "(Hheap & [%npc Hnpc] & Hpc & Hinstrs & %HsL)".
specialize (Hverif npc).
```

After the change `semTripleOneInstrStep` takes an `npc : RelVal ty_word`, its
PRE holds `lptsreg nextpc npc`, and the `specialize` line **disappears**. The
postcondition is unchanged (`∃ an, lptsreg nextpc an ∗ lptsreg pc an ∗ POST an`)
— that `∃` is real, it is the step's output.

### 3h. `Adequacy.v` — the loop invariant

Six sites forget the value: lines **1052, 1056, 1124, 1128, 1158, 1165**
(`∃ v, nextpc ↦ᵣ v`). The precondition sides (1052, 1124, 1158) must become
`nextpc ↦ᵣ anp` for the new executor argument; the postcondition sides (1056,
1128, 1165) should become `nextpc ↦ᵣ an` rather than `∃ v`, because the
recursive application needs the specific value to match the recursive call's
argument — and the epilogue already supplies exactly it.

**This is the one step with real shape risk**, since the invariant is shared
across iterations. If keeping it existential proves necessary, destructing at
the application site and passing the witness also works. Do this file last.

Nothing in `ImplPre`/`create_resources` changes: it already produces
`∃ v, nextpc ↦ᵣ v` **once**, which is what §3d's single demonic variable
consumes. **No trusted-statement-surface change** — verify before finishing,
this is the main reason this shape beats pinning.

### 3i. Not affected

`BlockVer/Verifier.v:103` and `BinaryBlockVer/Verifier.v:107` have their **own**
copies of the prologue/epilogue and are untouched. Confirm by grep afterwards.

---

## §4. Ordering

`Verifier.v` → `VerifierRel.v` (mirror → `rexec_instruction` →
`rexec_cfg_addr` → `sound_exec_instruction`) → `Adequacy.v` → examples.
Adequacy last: §3h is the only step with shape risk, and everything before it is
verifiable without it.

---

## §5. Validation

1. **Shape gate.** `Verifier.v` and `VerifierRel.v` compile (`vos`, then `full`).
   `rexec_instruction` still closes with one `rsolve`; `rexec_cfg_addr` still
   closes at all — no new `Admitted`, which is the whole point of this base.
2. **One example VC.** `solve_vc` on the cheapest example (Countdown) — the
   extra top-level demonic binder must not leave residuals.
3. **Measurement**, the point of the exercise. The flat reproducer at N=4 and
   N=8 against this base's own pre-change numbers. Report the exponent, not
   just the ratio, and measure back-to-back — per **rocq-timeout-triage** Step
   1b, wall times on this box swing with `.vo` page-cache state.
4. **Full gate** + `Print Assumptions countdown_noninterferent`: exactly
   `pure_decode` and `mmioenv`, as at `30c9517a`.

---

## §6. Afterwards: `encoded_instr`

Do **not** start it in the same commit. Land this, measure, then decide. The
options differ enough in cost that the measurement should inform the choice:

- give the encoding a function symbol instead of an existential — likely costs a
  new axiom next to `pure_decode`, i.e. a trusted-surface change;
- steer the solver's unification direction, which currently eliminates
  `result_fetch` in favour of `encoded_instr` (the losing direction) rather than
  the other way round.
