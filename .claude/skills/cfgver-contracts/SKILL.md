---
name: cfgver-contracts
description: >
  Katamaran CFGVer contracts in general — what a CFGVerifierContract IS and how to
  write one by hand. Use when asking about the contract record and its fields
  (cfg_init_addr, cfg_placement, cfg_exits, cfg_precondition, cfg_instrs,
  cfg_exitCond, cfg_fuel), choosing the logical context Σ ([ctx] concrete vs
  ["p"∷ty_xlenbits] parametric base), why the symbolic VC ignores cfg_init_addr and
  cfg_exitCond, ValidCFGVerifierContract / Valid_CFG_VC / DebugCFGVerifierContract,
  or hand-writing a contract without the generator (as for
  cmovznz4_cfg_contract_param) — including the assertion vocabulary: ↦ᵣ / ↦ₘ
  points-to, asn.exist, secLeakvar (leak permission for public values),
  asn_init_pc, and base-bound formulas. NOT for the gen_contract generator's spec
  lists (cfgver-gen-contract) and NOT for discharging VC residuals (cfgver-solve-vc).
---

# CFGVer contracts in general

What a contract *is* — independent of the `gen_contract` generator
(→ **cfgver-gen-contract**). Definitions in `CFGVer/Contracts.v`.

## The record

```coq
Record CFGVerifierContract {Σ} :=
  MkCFGVerifierContract
  { cfg_init_addr     : N
  ; cfg_placement     : Term Σ ty_xlenbits
  ; cfg_exits         : list (Term Σ ty_xlenbits)
  ; cfg_precondition  : Assertion (Σ ▻ "a" ∷ ty_xlenbits)
  ; cfg_instrs        : list AnnotInstr
  ; cfg_exitCond      : bv xlenbits -> bool
  ; cfg_fuel          : nat
  ; cfg_postcondition : Assertion (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits)
  }.
```

`cfg_instrs` used to be `list AST`; it is `list AnnotInstr` since the AnnotInstr
migration (PLAN-annotinstr.md Phase 1). `AnnotInstr` is a PRODUCT record —
`MkAnnotInstr { ai_ghost_before : list Annot ; ai_instr : AST ; ai_ghost_after :
list Annot }` — NOT the sum `AnnotAST | AnnotGhost` an earlier version of this
skill described; that sum was tried and reverted at `13eb91e0`, because it can
represent a ghost with no instruction to attach to. `Annot` is `AnnotDebugBreak`
(a transparent per-position heap/pathcondition dump) or `AnnotLemmaInvocation`
(a real `call_lemma`, since Phase 4 — see `cfgver-executor`).

`Verifier.v` declares a non-Local `AST -> AnnotInstr` coercion, so every existing
hand-written or `gen_contract`-built `cfg_instrs := <prog>_instrs` (a plain
`list AST`) still typechecks unedited — see **cfgver-executor** for the coercion
mechanics and `strip : list AnnotInstr -> list AST` (the trusted-layer projection
every ghost-blind consumer, e.g. `Noninterference.v`, actually sees).

| Field | Meaning |
|---|---|
| `Σ` | logical context: `[ctx]` for a concrete contract; `["p"∷ty_xlenbits]` for a parametric base (the base is then `term_var "p"`) |
| `cfg_placement` | where the code sits, as a **term**: `term_val … (bv.of_N ia)` concrete, `term_var "p"` parametric |
| `cfg_exits` | exit addresses as **terms** (built by `exits_of_offs` from base-relative offsets) — this is what the symbolic executor's exit choice checks against |
| `cfg_precondition` | `Assertion (Σ ▻ "a"∷ty_xlenbits)` — "a" is the start pc; parametric contracts must also include the base bound `unsigned p + size ≤ lenAddr` here, or fetch bounds are unprovable |
| `cfg_instrs` | the program, a `list AnnotInstr` placed at `cfg_placement` (coerces transparently from a plain `list AST` — see above) |
| `cfg_postcondition` | RE-EXPOSED 2026-09-03 (it had been hardwired to `true`). `consume`d at the moment the exit condition is hit, with `"an"` bound to whichever declared exit was taken; the soundness bridge hands it back to the caller, which is **what makes two segment contracts composable**. Pass `asn_no_post` for an ordinary whole-program contract. |
| `cfg_init_addr`, `cfg_exitCond` | **NOT used by the symbolic VC** (source comment on `Valid_CFG_VC`, `Contracts.v`) — carried for the end-to-end statement |

**The ignored-fields subtlety:** the VC dispatches exits against the *term table*
`cfg_exits`, not against `cfg_exitCond`. The two are reconnected only at the
end-to-end stage, by the `HexitOffs` premise of the `gen_contract_noninterferent_*`
bridges
(via `etable_faith_exits_of_offs`): every exit term must satisfy `exitCond`. A
hand-written contract whose `cfg_exits` and `cfg_exitCond` disagree will pass the
VC and fail there.

## Validity

```coq
Definition ValidCFGVerifierContract {Σ} (c : @CFGVerifierContract Σ) : Prop :=
  cfg_map c Valid_CFG_VC.
(* Valid_CFG_VC … := safeE (postprocess (CFG_VC_triple p exits P i fl)). *)
```

Discharge pattern: `Proof. vm_compute. solve_vc. Qed.` — residual patterns and
failure modes in **cfgver-solve-vc**.

**Debugging a failing VC:** `DebugCFGVerifierContract c` is the same VC wrapped as
a `VerificationCondition` instead of `safeE` — state it as a `Lemma`, `vm_compute`,
and read the residual instead of guessing.

## A contract may cover only PART of the program (sub-table contracts)

Since 2026-09-04 `cfg_instrs` need not be the whole program — it may hold only
the instructions the contract's segment actually executes, with the segment's
byte offset carried in **`cfg_placement`**:

```coq
cfg_placement := term_val ty_xlenbits (bv.of_N 256);   (* base + segment offset *)
cfg_instrs    := pl_seg;                               (* the SEGMENT only *)
cfg_exits     := exits_of_offs (term_val ty_xlenbits (bv.of_N 256)) [0%N];
```

`table_of_list p 0 seg` then emits exactly `256, 260, …`, so **no new record
field was needed** and `etable_faith_exits_of_offs` needs no change (it was
already placement-relative).

**Why bother:** a segment contract whose branch condition the solver cannot
decide by computation costs `93.81 + 4.05·P + 0.531·P²` M words in the number
`P` of *never-executed* instructions sharing its table — quadratic, held out to
+0.0024% at P=64 and +0.0079% at P=128, so **26.93× at 64 filler instructions**.
Trimming recovers all of it. On a *decidable*-branch segment the same axis is
only 1.35–1.60× on countdown but was measured at **3.03×** on real muladd (67%
of that segment's cost). Full record: `diagnostics/prefix-length-cost.md`.

**What you owe at the Iris level.** The caller owns `ptsto_instrs` of the WHOLE
program and must supply `itable_rel <whole-program map> <segment table>`. That
is `TablesRel.v`'s **`itable_faith_of_segment`**, over `Tables.v`'s three gmap
containments (`instrs_of_list_prefix` / `_suffix` / `_segment`). Nothing else
changes — `sound_scfg_verification_condition_myWP2` takes the map and the table
as separate arguments, so no resource splitting is needed and the continuation
hands the instruction ownership back.

Worked example: `Example/PaddedLoop.v` + `Example/PaddedLoopResult.v` (the
countdown loop inside a 66-instruction program; `pl_loop` is gate-checked
axiom-clean, and is the tree's ONLY proof whose table is a proper subset of the
program).

Three traps, each of which cost a compile:

- **`list_AST_AnnotInstr` is `List.map AST_AnnotInstr`, not an identity**
  (`Verifier.v:145`). Existing examples get away with writing a `list AST` only
  because the *record field* coerces it; `ptsto_instrs` and `itable_rel` will
  not. Symptom is an unresolved-implicit error on `<$>` ("Cannot infer the
  implicit parameter M of fmap"), which reads like an Iris notation bug.
- **Define the program AS the decomposition**: `padded_annot := pl_pre ++ pl_seg
  ++ pl_post` with all three at `list AnnotInstr`. Then
  `itable_faith_of_segment`'s `pre ++ seg ++ post` matches syntactically, which
  also avoids an `app_nil_r` rewrite that would otherwise hit the `seg`
  occurrence inside `table_of_list` too.
- **`itable_faith_of_segment`'s `pre`/`seg`/`post` are EXPLICIT** (only `Σ`,
  `cbase`, `off` are implicit — `length pre` is not a rigid position, and
  `Set Implicit Arguments` marks only strict implicits). `off` is inferable from
  nothing, and `(off := _)` fails with *"Not enough non implicit arguments"*.
  Use the fully-`@` form: `@itable_faith_of_segment Σ p ι cbase off pre seg post`.

## Hand-writing a contract: the assertion vocabulary

A hand-written precondition is built from exactly what the generator would emit
(cf. `gen_reg_asn`/`gen_mem_asn` in **cfgver-gen-contract-internals**):

| Assertion | Meaning |
|---|---|
| `r ↦ᵣ t` / `t_addr ↦ₘ t_val` | register / memory-word points-to (terms) |
| `asn.exist "v" ty_xlenbits (…)` | existentially quantified value ("some value") |
| `secLeakvar "v"` | **leak permission**: the value of `"v"` is public — allowed to influence leakage. Its *absence* is what makes a value secret |
| `asn_init_pc t` | the start pc `"a"` equals `t` |
| `asn.formula (formula_relop …)` | pure side conditions — e.g. the parametric base bound `unsigned p + size ≤ lenAddr` |

So: public register = `asn.exist "v" … (r ↦ᵣ term_var "v" ∗ secLeakvar "v")`;
private = the same without `secLeakvar`; pinned = `r ↦ᵣ term_val … v` directly.

### `∗` ORDER MATTERS in a consumed assertion — put pure conjuncts LAST

`∗` is commutative, so the order of conjuncts does not change what a
precondition *means* — but it does change the VC you get, so it is not a free
choice. `consume` walks `∗` strictly left-to-right, and a `SepContract`'s logic
variables arrive as unconstrained ANGELIC evars (`call_contract`; only the ones
appearing in `sep_contract_localstore` are pinned up front, by `assert_eq_nenv`).
A pure conjunct — `secLeakvar "x"`, `asn.formula …` — placed **before** the
chunk that pins `"x"` is therefore asserted about an evar nothing is known
about, cannot be discharged, and leaks one residual per call into the VC. Worse,
`postprocess`'s `solve_evars` substitutes the variable afterwards, so the
leftover *prints* as something trivially true and reads as a solver bug.

So: **a pure conjunct goes after whatever chunk pins its variable.** Measured
2026-07-29 (commit `55421905`) on `sep_contract_fetch_instr`, whose localstore is
`[]`: moving `secLeakvar "a"` after `asn.chunk (chunk_ptsreg pc (term_var "a"))`
removed all 28 `secLeak` asserts from `key_schedule_loop2`'s VC and shrank it
3.17 MB → 524 KB. `checked_mem_write` / `mem_write_value` already followed the
rule.

**The exception — do NOT move a conjunct past a PATTERN MATCH on its own
variable.** Crossing a chunk only adds an equation, so it is information-
preserving. `asn.match_bool (term_var "inv")` instead *eliminates* `inv`: after
it, `secLeakvar "inv"` says only "this literal is public", and the precondition
genuinely weakens. `checked_mem_read` / `mem_read` therefore keep their
`secLeakvar "inv"` in front — moving it makes `valid_checked_mem_read`
unprovable against its own body (all three `restrict_bytes` cases reduce to
`false = true`). Their leftover is `secLeak <literal>`, which `solve_vc` closes
trivially, so it costs nothing. Mechanism: **core-executor-internals**;
diagnosing such a residual: **cfgver-solve-vc**.

Exemplar: `cmovznz4_cfg_contract_param` (`Example/Cmovznz4.v`) — `Σ = ["p"∷ty_xlenbits]`,
placement `term_var "p"`, exits at `bvadd p (of_N off)` terms, precondition with
the base bound plus register/memory assertions. Two rules of thumb:

- Build addresses as `bop.bvadd (term_var "p") (term_val … (bv.of_N off))` — only
  concrete offsets under `bv.of_N`; a symbolic argument to `bv.of_N` makes
  `vm_compute` diverge.
- There is also a notation `{{ P }} i @cfg[ ec , fl ]` for concrete contracts
  at `init_addr`, kept `Local` in `Example/MvSwap.v` (its only user) because it
  turns `{{`/`}}` into lexer keywords that break any other `}}` occurrence.

**Consuming a contract:** the once-and-for-all route is
`gen_contract_noninterferent_param` / `_rel*` (generator contracts,
→ **cfgver-gen-contract**);
hand-written contracts wire through `cfg_instrs_endToEnd` (→ **cfgver-endtoend**).
