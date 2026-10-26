---
name: cfgver-contracts
description: >
  Katamaran CFGVer contracts in general — what a CFGVerifierContract IS and how to
  write one by hand. Use when asking about the contract record and its fields
  (cfg_placement, cfg_exit — the single exit address term —,
  cfg_precondition, cfg_instrs, cfg_fuel, cfg_postcondition), choosing the logical
  context Σ ([ctx] concrete vs ["p"∷ty_xlenbits] parametric base), why a contract
  carries no load address (cfg_init_addr is gone; the bridges take init_addr),
  ValidCFGVerifierContract / Valid_CFG_VC / DebugCFGVerifierContract,
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
  { cfg_placement     : Term Σ ty_xlenbits
  ; cfg_exit          : Term Σ ty_xlenbits
  ; cfg_precondition  : Assertion (Σ ▻ "a" ∷ ty_xlenbits)
  ; cfg_instrs        : list AST
  ; cfg_fuel          : nat
  ; cfg_postcondition : Assertion (Σ ▻ "a" ∷ ty_xlenbits ▻ "an" ∷ ty_xlenbits)
  }.
```

`cfg_instrs` is a plain `list AST` (again) since 2026-09-22
(`plans/PLAN-contract-ast.md` Phase 1, `da4f5b4e`): annotations are TOOL INPUT,
passed to the verification as a separate argument — the VC is `cfg_vc c a` with
`a : list AnnotInstr` whose `strip` must equal `cfg_instrs c` — not carried in
the specification. (Between the AnnotInstr migration and that date the field
WAS `list AnnotInstr`; this is also what lets `ai_block` carry a real contract
without a circularity.) `AnnotInstr` is a PRODUCT record —
`MkAnnotInstr { ai_ghost_before : list Annot ; ai_instr : AST ; ai_ghost_after :
list Annot }` — NOT the sum `AnnotAST | AnnotGhost` an earlier version of this
skill described; that sum was tried and reverted at `13eb91e0`, because it can
represent a ghost with no instruction to attach to. `Annot` is `AnnotDebugBreak`
(a transparent per-position heap/pathcondition dump) or `AnnotLemmaInvocation`
(a real `call_lemma`, since Phase 4 — see `cfgver-executor`).

`Verifier.v` declares a non-Local `AST -> AnnotInstr` coercion, so a plain
`list AST` can be passed where the annotated list `a` is expected — see **cfgver-executor** for the coercion
mechanics and `strip : list AnnotInstr -> list AST` (the trusted-layer projection
every ghost-blind consumer, e.g. `Noninterference.v`, actually sees).

| Field | Meaning |
|---|---|
| `Σ` | logical context: `[ctx]` for a concrete contract; `["p"∷ty_xlenbits]` for a parametric base (the base is then `term_var "p"`) |
| `cfg_placement` | where the code sits, as a **term**: `term_val … (bv.of_N ia)` concrete, `term_var "p"` parametric |
| `cfg_exit` | the ONE exit address, as a **term** (usually `exit_of_off p off`, `Tables.v`). A run stops exactly when pc = exit (except at the entry step). Replaced `cfg_exits`/`cfg_exitCond` on 2026-09-25 (`plans/PLAN-exit-targets.md`) |
| `cfg_precondition` | `Assertion (Σ ▻ "a"∷ty_xlenbits)` — "a" is the start pc; parametric contracts must also include the base bound `unsigned p + size ≤ lenAddr` here, or fetch bounds are unprovable |
| `cfg_instrs` | the program, a `list AST` placed at `cfg_placement`; the annotated copy is `cfg_vc`'s second argument (see above) |
| `cfg_postcondition` | RE-EXPOSED 2026-09-03 (it had been hardwired to `true`). `consume`d at the moment the pc reaches the exit, with `"an"` bound to `cfg_exit`; the soundness bridge hands it back to the caller, which is **what makes two segment contracts composable**. Pass `asn_no_post` for an ordinary whole-program contract. |
| *(no load address)* | The old `cfg_init_addr : N` field was DROPPED 2026-09-28 (PLAN-valid-blk-annot §8.2): the VC never read it and, once `ValidCFGVerifierContract` stopped quoting it, nothing did. A contract says where its code is only through the `cfg_placement` term; the end-to-end bridges take `init_addr` themselves and link it by `inst (cfg_placement c) ι = SyncVal (bv.of_N init_addr)`. So a parametric contract is a CLOSED term (no `ia` argument) |

The exit is stored once. The end-to-end stage relates it to the trusted
statement's literal `exit_addr : N` through the `HexitFaith : etable_rel
(SyncVal (bv.of_N exit_addr)) (cfg_exit contract) ι` premise (discharged by
`etable_faith_exit_of_off`, `TablesRel.v`; the generator bridges do it
internally).

## Validity

> **Loops (PLAN-loop-rule.md, 2026-10-14):** a loop is a LOOP CONTRACT,
> proved by its own VC `cfg_vc_loop c a` — one run of the body from the
> invariant (the precondition), stopping at the exit (owing the post) or back
> at the head (owing the invariant). Parameters = what never changes; every
> changing variable is existential inside the invariant; the post mentions
> parameters only. No annotation marks the loop. Partial correctness: the
> invariant must be preserved, not ensure termination. See **cfgver-executor**,
> "Loops: the LOOP VC".

```coq
(* Contracts.v -- THE VC, over an annotated copy `a` of the program *)
Definition cfg_vc {Σ} (c : @CFGVerifierContract Σ) (a : list AnnotInstr) : Prop :=
  cfg_map c (fun p exits P _ fl Q => Valid_CFG_VC p exits P a fl Q).
(* Valid_CFG_VC p exit P i fl Q := safeE (cfg_postprocess (CFG_VC_triple p exit P i fl Q)),
   cfg_postprocess = postprocess o SPureSpec.replay o postprocess (since 2026-10-01). *)

(* Validity.v (heavy, small; re-exported by EndToEnd.v) -- the SEALED
   property, built only via ValidCFGVerifierContract_intro / solve_valid *)
Definition ValidCFGVerifierContract {R} (c : @CFGVerifierContract R) : Prop :=
  exists LV : list (AnnotInstrV blkValid),
    cfg_vc c (map eraseV LV)
    /\ map aiv_instr LV = cfg_instrs c.
(* The witness is TYPED (2026-09-29): each block carries its blkValid proof
   (vb_ok), so no validity predicate is proved about the list. *)
```

This is what EVERY bridge takes (`EndToEnd.v`, `GenCompose.contract_run` /
`seg_run` / `loop_*`): annotations appear only where the contract is proved
valid. `solve_valid <VC>` closes it for a block-free program. A program with
blocks writes its `LV` in the heavy Result file (blocks as
`MkBlkAnnotV b b_valid`) and uses
`@ValidCFGVerifierContract_intro _ c LV` with `[exact <light VC> | reflexivity]`
— the light VC over the erased literal is accepted BY
CONVERSION (`Example/CountdownRecResult.cdLink_valid`). `annotsValid` still
exists, but only on the way out (`_elim`, via `annotsValid_of_V`).

`cfg_vc` does not force `strip a = cfg_instrs c`; that equation is a premise of
the soundness bridge, so a VC over the wrong `a` proves nothing usable.

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
cfg_exit      := exit_of_off (term_val ty_xlenbits (bv.of_N 256)) 0%N;
```

`table_of_list p 0 seg` then emits exactly `256, 260, …`, so **no new record
field was needed** and `etable_faith_exit_of_off` needs no change (it is
placement-relative).

**Why bother:** a segment contract whose branch condition the solver cannot
decide by computation costs `93.81 + 4.05·P + 0.531·P²` M words in the number
`P` of *never-executed* instructions sharing its table — quadratic, held out to
+0.0024% at P=64 and +0.0079% at P=128, so **26.93× at 64 filler instructions**.
Trimming recovers all of it. On a *decidable*-branch segment the same axis is
only 1.35–1.60× on countdown but was measured at **3.03×** on real muladd (67%
of that segment's cost). Full record: `diagnostics/prefix-length-cost.md`.

**What you owe at the Iris level.** The caller owns `ptsto_instrs P` of the
WHOLE program (`P : gmap _ AST`) and runs the segment with
**`GenCompose.contract_run`** (PLAN-valid-blk-annot V11), whose only table-side
premises are the placement, a no-wrap fit, and the AST containment
`instrs_of_list pbase (cfg_instrs c) ⊆ P` — typically from `Tables.v`'s
`instrs_of_list_segment` lifted by `map_fmap_mono`. `contract_run` derives
table faithfulness itself; no resource splitting is needed and the continuation
hands the instruction ownership back. (The annotation-level
`itable_faith_of_segment` it replaced was deleted in Phase 5.)

**Prefer a BLOCK to a hand-composed sub-table cut (2026-10-01).** The old worked
example here, `PaddedLoopResult.pl_loop` (two segment contracts glued in Iris by
`contract_run` + `myWP2_loop_induction`), was migrated to a loop block:
`Example/PaddedLoop.v` now runs a 66-instruction program whose loop at offset
256 is ONE block (`CountdownRec.cdRecBlk`, valid at every address), and
`PaddedLoopResult.padded_loop_noninterferent_param` is the gate-checked end
theorem. The block's table is a proper subset of the program, checked by
`blk_code_in`. The hand-written Iris version framed the whole 66-entry
instruction map by `cbn`/`iFrame` and peaked at ~9.4 GB (170 s); the block
version is 27 s / 7.3 GB with no hand-written Iris. No end theorem uses
`instrs_of_list_segment` any more; `contract_run` is still exercised by the
other composed examples (`SwapComposedResult`, `CountdownComposedResult`,
`TwoLoopsComposedResult`).

Two traps, each of which cost a compile:

- **`list_AST_AnnotInstr` is `List.map AST_AnnotInstr`, not an identity**
  (`Verifier.v:145`). Existing examples get away with writing a `list AST` only
  because the *record field* coerces it; `ptsto_instrs` and `itable_rel` will
  not. Symptom is an unresolved-implicit error on `<$>` ("Cannot infer the
  implicit parameter M of fmap"), which reads like an Iris notation bug.
- **Define the program AS the decomposition**: `padded_annot := pl_pre ++ pl_seg
  ++ pl_post` with all three named. Then `instrs_of_list_segment`'s
  `pre ++ seg ++ post` matches syntactically, which avoids an `app_nil_r`
  rewrite.

## Arrays: the `arrv` chunk and the CFGVer ghost-lemma catalogue

`arrv w s t [a; n; e; vs]` (`Sig.v`): n cells of **w bytes** at a, a+s, …,
a+s(n-1), cell i holding the i-th element of `vs`, and e = a + s·n.
w = |s| tiles (words `4 4`/`4 (-4)`, bytes `1 1`); |s| > w is an array of
structs. a, n, e must be public (interp is False on NonSyncVal) — state
`secLeakvar` of the count in a loop invariant; the executor does not infer it.
Ghost lemmas are `Verifier.CLem` constructors (`clem_arrv_*`), used as
`AnnotCLemma (...)` in `ai_ghost_before/after`; soundness `SpecIris.clemSem`.
The array argument is matched ANGELICALLY. Loop template:
`Example/Muladd/MuladdParamLoopN.v` (remaining count n the only varying
variable, addresses END − s·n). It replaced `arr pub w s [a; n; e]` (a `pub`
flag, existential values), deleted 2026-10-26 (PLAN-arrv Phase E; old text
in `.claude/archive/arr-removal-2026-10-26.md`) — with it went the
halfword/doubleword regroups (`RgWidth`): `arrv` regroups words only.

**The values and the tag (PLAN-arrv).** `t : string` is a TAG (D14): a Coq-level index the Iris
interpretation ignores, whose only job is to tell same-shape arrays apart in
the executor's angelic chunk match (without it, every match among same-shape
arrays branched per candidate, `diagnostics/arrv-loop-cost-drivers.md`). It
is NOT a logic variable — a callee would bind that angelically and the
ambiguity would return. Conventions: a top-level `DArr`/`DBytes` array's tag
is its value name (D15, `gen_data_at`); a template takes its arrays' tags as
Coq parameters (D16: `LoopN`'s `ln_tm ln_tx ln_tdm ln_tdx`, RSA's
`sub_mem ta tb`); every lemma names the tag of EACH array it matches (D17):
`join w s t1 t2 t` (result `t`), `lockstep w s t1 t2`, `pad w s t t'`, all
others one `t`, kept — `flip` included, so a done array keeps its tag until a
`join` gives the result the source's (`join "db" "vb" "vb"`, RsaSpikeSub).
A tag mismatch is a FAILED match, not an ambiguity: the ghost or block
consume errors. `vs : list (bvec 8w)`, no publicness flag: a public
array is `arrv … vs ∗ secLeak vs`, and a plain take hands publicness to the
parts (the take's `vs = x :: r` is `formula_propeq`, Leibniz on RelVal, and a
lifted op is SyncVal iff its arguments are), so there are no `_pub` lemma
variants. That hand-off is done by the SOLVER (`Solver.v` `ResimpSecLeak`,
2026-10-25): when a unification substitutes `vs := x :: r`, the old
`secLeak vs` is re-split into `secLeak x`, `secLeak r`. Before it, the split
happened only by luck of tree shape (a `replay` of a hoisted var-eq) and
failed after a load or under an angelic choice between same-shape arrays
(`Example/Rsa/RsaSpikeSb.v` `valid_cpy`). Catalogue (`clem_arrv_*`): `take_first` (equation, for a variable
value) / `take_cons` (pattern on a syntactic `x :: r`), `take_last`
(`vs = r ++ [x]`), `add_first` (`x :: vs`), `add_last` (`vs ++ [x]`),
`nonempty`, `empty` (`⊢ arrv a 0 a []`, `a` bound later by an ANGELIC match),
`empty_at t t'` (`arrv t a … ⊢ itself ∗ arrv t' a 0 a []` — a seed at an
existing array's start; use it when the seed is also made on a path that
SKIPS the loop, e.g. memcpy's `beqz n, ret`: there `empty`'s address is never
pinned and a later `join`'s plain match fails, `Example/Rsa/RsaMemcpy.v`),
`empty_elim` (`a = e` only — never `vs = []`: `NonSyncVal [] []` exists),
`lockstep`, `drop`, `flip` (`rev vs`; `peval_rev` normalises to snoc form),
`join` (`v1 ++ v2`, no overflow premise: the count is the length mod 2^32),
`pad` (`arrv a n e vs ∗ arrv b 0 c ws ⊢ arrv a n e (vs ++ ws) ∗ …`, w ≥ 1),
`split k` (`vs = v1 ++ v2`), and the word ⇄ byte VIEW of a value:
`to_bytes` (`arrv 4 4 a n e ws ⊢ arrv 1 1 a (4 *ᵇ n) e (regroup ws)`) and
`of_bytes` (PATTERN form: `arrv 1 1 a (4 *ᵇ k) e (regroup v) ∗ k <u 2^30 ⊢
arrv 4 4 a k e v` — the bound is needed, ·4 is not injective mod 2^32).
`uop.regroup` splits each cell into its little-endian bytes (`bv.le_bytes`,
memory order). The byte count must stay syntactically `4 *ᵇ k`: a program's
`slli k,2` normalises to it, but a word count that is a ring SUM (n+1) does
not survive (`4·(n+1)` becomes `4 + 4·n`) — name such a count. Worked probes
with negative controls: `Example/Rsa/ZZArrvCatalogue.v`,
`Example/Rsa/ZZArrvWords.v` (a public header WORD survives a BYTE memcpy);
soundness: `SpecIris.clem_arrv_*_sound`.

**Tracking a read-only array's value through a loop** (PLAN-arrv D13,
`MuladdParamLoopN.v` since 2026-10-24): the loop's done array (stride −s,
grown by `add_first`) and the remaining source satisfy `VM = rev dM ++ rM`
with `VM` a CONTRACT variable (instantiated angelically at entry: `[]` seed,
`rM := vb`); after the loop, `flip` the done array (`rev dM`, forward) and
`join` it with the emptied source (`rev dM ++ rM`), and the post can state
the array with its pre value. An overwritten array's value is just ∃. Worked
case with negative controls (a cannot come back unchanged, nor public):
`Example/Rsa/RsaSpikeSub.v` (`sub_mem_out`). **Cost: back to `arr`'s with
the tag** — untagged, angelic ambiguity between same-shape arrays made LoopN
≈3.7× arr warm and trapped the value ∃s under the choice; tagged it is
≈1.13× (9.7 vs 8.6 s warm, 0 surviving ∃), the callee 23.6 → 3.4 s cold.
`diagnostics/arrv-loop-cost-drivers.md` §7.

**Ghosts on an instruction that carries a block NEVER RUN** (`Verifier.v`,
the `Some b` branch of the step: the block fires INSTEAD of the instruction,
ghosts included). Seeds for a loop block's done arrays (`clem_arrv_empty`) go
in `ai_ghost_after` of the instruction BEFORE the block — muladd's tail puts
`build_i` after index 66 for its block at 67. Symptom of getting it wrong: the
loop block's entry fails to match a done array that is simply absent from
the heap (found 2026-10-22, PLAN-rsa.md Phase 1). Ghosts AFTER a block's exit
go on the instruction at the exit (`ai_ghost_before`), which is not a block.

**Entering LoopN from a precondition whose count is `m − 1`** used to fail
outright: the source-array start `end − 4·count` then carries the SAME literal
(+4) as a heap start `4 + x`, the solver cancelled it and eliminated the
PARAMETER x instead of the loop's evar. Fixed in the solver
(`try_isolate_inner`, core-executor-internals); muladd's counts (`mlen − 3`)
never hit it by luck of literals.

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
`false = true`). Their leftover is `secLeak <literal>` (after `solve_evars`),
which `solve_vc` closes trivially — but it is NOT free: as an `assertk` in the
tree it stops `postprocess` hoisting a later var-eq above earlier assumes, so
every LOAD changes which facts `replay` can re-simplify (this is what hid the
unsplit-`secLeak` bug fixed by `ResimpSecLeak`, 2026-10-25, see the arrv
paragraph above). Mechanism: **core-executor-internals**;
diagnosing such a residual: **cfgver-solve-vc**.

Exemplar: `cmovznz4_cfg_contract_param` (`Example/Cmovznz4.v`) — `Σ = ["p"∷ty_xlenbits]`,
placement `term_var "p"`, exit at a `bvadd p (of_N off)` term, precondition with
the base bound plus register/memory assertions. Two rules of thumb:

- Build addresses as `bop.bvadd (term_var "p") (term_val … (bv.of_N off))` — only
  concrete offsets under `bv.of_N`; a symbolic argument to `bv.of_N` makes
  `vm_compute` diverge.
- There is also a notation `{{ P }} i @cfg[ fl ]` for concrete contracts
  at `init_addr`, kept `Local` in `Example/MvSwap.v` (its only user) because it
  turns `{{`/`}}` into lexer keywords that break any other `}}` occurrence.

**Consuming a contract:** the once-and-for-all route is
`gen_contract_noninterferent_param` / `_rel*` (generator contracts,
→ **cfgver-gen-contract**);
hand-written contracts wire through `cfg_instrs_endToEnd` (→ **cfgver-endtoend**).
