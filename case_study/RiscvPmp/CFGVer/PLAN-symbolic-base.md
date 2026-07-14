# Plan: CFGVer verification at a symbolic (parameterized) base address

Status: probes complete, design locked (2026-07-14). This document is the
execution plan. It is written to be executable by a fresh session (Opus or
Sonnet) with `CLAUDE.md` and the project memory loaded. Read the whole plan
before starting any phase.

---

## 0. Context and non-negotiable design decisions

**Goal.** Verify CFG programs once, for *every* placement of the code in
memory: the CFG verifier's symbolic executor must run with the program's base
address as a symbolic term, ending in a `<prog>_noninterferent` theorem
quantified over the base (with a memory bound).

**What already exists (do not redo):**
- Commit `f0cc9739`: `peval_bvadd` folds constant-headed sums
  (`c1 ⊕ (c2 ⊕ t)` and `(c1 ⊕ t) ⊕ c2` → `(c1+c2) ⊕ t`). Consequence,
  *empirically confirmed by probes*: the pc term after k steps through the
  real step semantics is canonically `term_bvadd (term_val (4k)) base`
  (constant first). The whole design leans on this.
- Probes (see memory `project-cfgver-symbolic-base-spike`): two full
  instructions execute at a symbolic base with no error; secLeak asserts
  decompose structurally (`simplify_secLeak`, `theories/Symbolic/Solver.v:2229`);
  the residual VC obligations are (a) `secLeak(var)` atoms, (b) occasionally a
  compound `secLeak(4k ⊕ a)`, (c) fetch bounds `0 ≤ unsigned pc_k` and
  `unsigned pc_k + 4 ≤ 1024` with `unsigned (4k ⊕ a)` NOT distributed.

**Locked decisions — do not re-litigate, do not "simplify" away:**

1. **Instruction dispatch is a syntactic term-table lookup.** The symbolic
   executor takes a table of (address *term*, instruction) pairs and matches
   the current pc against keys via `Term_eqb (peval apc) (peval key)`. No
   match → `error`. This IS the state-explosion safeguard: branching factor 1,
   loud failure, never enumerate.
2. **No base parameter in Verifier.v, no binding of initial pc to a base.**
   Placement knowledge lives only in the table keys the caller (Examples.v)
   constructs. Entry point is wherever the contract precondition puts `a`.
3. **The concrete executor and the entire soundness chain below the
   refinement are untouched**: `cexec_cfg_addr` keeps `gmap (bv xlenbits) AST`
   (absolute addresses), `exitCond : bv xlenbits -> bool`, `RVToOption`
   NonSyncVal rejection; `sound_exec_cfg_addr`, `ptsto_instrs`, all memory
   lemmas in Examples.v stay as-is.
4. **The bridge is a faithfulness hypothesis** relating the symbolic table to
   the concrete map, in the **∃-SyncVal form** (NOT the implication form):
   `∀ (t,i) ∈ table, ∃ v, inst t ι = SyncVal v ∧ instrs !! v = Some i`.
   The ∃-form is load-bearing: if a key could instantiate to `NonSyncVal`,
   the symbolic side would proceed while the concrete side errors at
   `RVToOption`, making the refinement unprovable. Exit table analogously:
   `∀ t ∈ exits, ∃ v, inst t ι = SyncVal v ∧ exitCond v = true`.
   (Semantically complete: the pc is leaked each step, so instruction
   addresses are public in any verifiable contract.)
5. **Never ask the solver to cancel bvadd.** All base/offset reasoning is
   syntactic-modulo-peval, or value-level Coq lemmas. If a proof obligation of
   the form `base ⊕ x = base ⊕ y → x = y` appears at solver level, the design
   has been violated — stop and reassess.
6. **Bounds discharge = helper lemma + `solve_vc` extension** (user's explicit
   choice), NOT a user-solver simplification rule. The solver/TCB is not
   extended.

**Rejected alternatives (one line each, so nobody re-walks these):**
- *base⊕offset accumulator in the executor state*: dies on solver-level
  re-splitting after each step (branch `wip/cfgver-base-offset-split`).
- *offset-keyed shared gmap*: forces rebasing `ptsto_instrs` + rewriting all
  Examples.v memory lemmas + offset-relative exitCond through the whole chain.
- *exit-offsets protocol replacing exitCond*: interface churn rejected as
  complexity regression.
- *CanonTerm/TermRing polynomial normal forms*: infra unfinished (commented
  out of `peval`), not needed.
- *Countable instance for Term to key a gmap by terms*: instance is a
  multi-day dependent-encoding project; gmap lookup is exact-syntactic, but we
  need lookup-modulo-peval; persist would rebuild the map anyway. Association
  list wins.

---

## 1. Phase 0 — Helper lemmas (self-contained, no signature changes)

**Files:** `case_study/RiscvPmp/CFGVer/Examples.v` (or a small new helper
section; keep them where `solve_vc` can use them).
**Model:** Sonnet. **Gate:** lemmas compile `mode=full`; existing files
unaffected.

1. **Compound secLeak discharge.** The residual obligation shape (probe 2):
   asserted `formula_secLeak (term_bvadd (term_val c) t)` under an assumption
   `formula_secLeak t`. Prove a helper by composing the existing
   `instpred_formula_secLeak_binop` (Solver.v, ⊣⊢) and
   `instpred_formula_secLeak_val`, then add a `try (apply ...)` step to
   `solve_vc`'s repertoire. Two lemma applications; check the exact `instpred`
   phrasing the VC leaves (run a probe VC first — don't guess).
2. **Fetch-bounds discharge.** Obligation shapes at step k (probe-confirmed,
   stated over `ty.int` via `term_unsigned`):
   - `0 ≤ unsigned pc_k` — always true (`bv.unsigned` is a `Z.of_N`); tiny lemma.
   - `unsigned pc_k + 4 ≤ 1024` where `pc_k = bv.add (bv.of_N (4k)) a`.
   Helper (value-level, N or Z to match `instpred`):
   ```coq
   Lemma fetch_bound_step (a : bv xlenbits) (c X : N) :
     (bv.bin a + X <= 1024)%N -> (c + 4 <= X)%N ->
     (bv.bin (bv.add (bv.of_N c) a) + 4 <= 1024)%N.
   ```
   Core step: `bv.bin (bv.add (bv.of_N c) a) = c + bv.bin a` under
   no-overflow — use `bv.bin_add_small` + `bv.bin_of_N_small`
   (`c + bv.bin a ≤ 1024 < 2^32`). Then extend `solve_vc` to apply it, feeding
   the bound from the contract precondition.
   **Traps (CLAUDE.md pitfall table has both):** the Zify rewrite on
   `bv.bin (bv.of_N x)` breaks `lia` — use
   `set (B := bv.bin (bv.of_N _)) in *; clearbody B` first; and never let
   `lia` see the literal `2^32` — bound through small literals or
   `set (E := bv.exp2 xlenbits); clearbody E`.

---

## 2. Phase 1 — Symbolic executor rewrite (`CFGVer/Verifier.v`)

**Model:** Sonnet with this plan; escalate to Opus on friction.
**Gate:** `Verifier.v` compiles `mode=vos` (statements) — the relational
section will be broken until Phase 2; comment it out temporarily with a
`TODO(symbolic-base)` marker if needed, mirroring how the gmap pivot handled
`AnnotatedBlockVerification`.

1. **World-indexed table types** (tables contain world-dependent terms, so
   they must be TYPE-level and passed through the recursion, not fixpoint
   parameters):
   ```coq
   Definition SITable : TYPE :=
     fun w => list (Term (wctx w) ty_xlenbits * AST).
   Definition SETable : TYPE :=
     fun w => list (Term (wctx w) ty_xlenbits).

   Definition persist_itable {w1 w2} (θ : Acc w1 w2) : SITable w1 -> SITable w2 :=
     List.map (fun '(t,i) => (persist__term t θ, i)).
   (* persist_etable analogous *)

   Definition lookup_instr {w} (tbl : SITable w)
       (apc : STerm ty_xlenbits w) : option AST :=
     option_map snd
       (List.find (fun '(t,_) => Term_eqb (peval apc) (peval t)) tbl).
   Definition is_exit {w} (exits : SETable w)
       (apc : STerm ty_xlenbits w) : bool :=
     List.existsb (fun t => Term_eqb (peval apc) (peval t)) exits.
   ```
   The `peval` on BOTH sides is required: solver substitutions (e.g.
   `p := term_val 256` in the concrete case) leave keys unnormalized
   (`8 ⊕ 256`) while the semantics-produced pc is normalized (`264`).
2. **`sexec_cfg_addr`** — keep today's shape exactly (angelic_binary, error
   messages), swap the guard and lookup:
   ```coq
   Fixpoint sexec_cfg_addr (fuel : nat) :
     ⊢ SITable -> SETable -> STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits) :=
     fun w tbl exits apc =>
       match fuel with
       | O => emsg "out of fuel"
       | S n' =>
           angelic_binary
             (if is_exit exits apc then pure apc
              else emsg "exit branch: pc matches no declared exit term")
             (match lookup_instr tbl apc with
              | None => emsg "no instruction key matches this pc term"
              | Some i =>
                  ⟨ θ1 ⟩ apc' <- sexec_instruction i apc ;;
                  sexec_cfg_addr n' (persist_itable θ1 tbl)
                                    (persist_etable θ1 exits) apc'
              end)
       end.
   ```
   (Adapt to the file's ⟨θ⟩-bind notation; `term_get_val` disappears.)
3. **`sexec_triple_addr` / `sblock_verification_condition`**: take
   `(tbl : list (Term Σ ty_xlenbits * AST)) (exits : list (Term Σ ty_xlenbits))`
   over the contract context Σ instead of `(instrs : gmap …) (exitCond)`.
   After `demonic_ctx` yields `δ : Sub Σ w`, move the tables into the world by
   `subst`-ing keys with δ (same mechanism that instantiates `req`).
4. Concrete side (`cexec_*`, `Monotonic` instances, Shallow section):
   **unchanged**.

---

## 3. Phase 2 — Refinement (`CFGVer/Verifier.v`, relational section)

**Model:** STRONG (Opus or Fable). This is where the known multi-hour hazards
live. **Gate:** `Verifier.v` compiles `mode=full`.

1. **Faithfulness relations.** Two Rel-level statements (as iProp premises in
   the UnifLogic, pure + persistent so they survive world evolution):
   - instr: `∀ (t,i) ∈ tbl, ∃ v, repₚ (SyncVal v) t ∗ ⌜instrs !! v = Some i⌝`
     — or the `⌜inst t ι = SyncVal v⌝` phrasing, whichever composes with
     `repₚ_antisym_left`-style lemmas better. **Must be the ∃-SyncVal form**
     (decision 4).
   - exit: `∀ t ∈ exits, ∃ v, repₚ (SyncVal v) t ∗ ⌜exitCond v = true⌝`.
   Package so that `forgetting_unconditionally_drastic` can project them into
   the IH world (pure facts + `inst`∘`persist` composition; prove one
   `faithful_persist` lemma per table).
2. **`rexec_cfg_addr`** restated:
   `faithfulness hyps ⊢ ℛ⟦RVal ty_xlenbits -> RHeapSpec (RVal ty_xlenbits)⟧
   (cexec_cfg_addr instrs exitCond fuel) (sexec_cfg_addr fuel tbl exits)`.
   Proof skeleton mirrors the existing one (iInduction fuel; `+` for
   angelic_binary arms, `--` for refine_bind, `*` for lookup cases):
   - Exit arm: `is_exit` true → find the matching exit term `t`; `Term_eqb`
     reflection (`Term_eqb_spec`) gives `peval apc = peval t`; via
     `peval_sound` both instantiate equally; exit faithfulness gives
     `inst apc ι = SyncVal v` with `exitCond v = true` → the concrete exit arm
     `if exitCond v then pure` succeeds on the related value.
   - Execute arm: `lookup_instr = Some i` → matched key `t`, same reasoning
     gives `inst apc = SyncVal v` and `instrs !! v = Some i` → concrete
     `RVToOption` succeeds and `instrs !! v` takes the same branch; then
     `refine_bind` + existing `rexec_instruction` + IH on persisted tables
     (via `faithful_persist`).
   - `None`/`false` → symbolic `error` → `rsolve` closes (nothing to prove).
   **Known traps:** the scrutinee of `match lookup_instr …` inside ℛ⟦⟧ carries
   hidden instance implicits — `destruct` by capturing the goal's exact
   scrutinee with `lazymatch goal with |- context[match ?x with …] =>
   destruct x end` (CLAUDE.md pitfall). `rsolve` failures → `Set Typeclasses
   Debug.` and add the missing `RefineCompat` instance; the new sexec needs
   its own `refine_compat_exec_cfg_addr` carrying the faithfulness premises.
3. **`rexec_triple_addr` / VC-level refinement**: thread the tables and
   faithfulness through; `sblock_verification_condition`'s refinement gains
   the same premises.

---

## 4. Phase 3 — Soundness plumbing (`CFGVer/Examples.v`)

**Model:** Opus preferred (Sonnet acceptable with care).
**Gate:** Examples.v compiles `mode=full` with existing examples re-verified.

1. `sound_exec_cfg_addr_myWP2`, `sound_cexec_triple_addr_myWP2`: concrete —
   **unchanged**. `sound_sblock_verification_condition_myWP2`: statement now
   takes the table VC (`safeE (postprocess (sblock_verification_condition
   … tbl exits …))`) plus Coq-level faithfulness facts at the given ι, and
   concludes the same myWP2 statement about `gmap` + `exitCond`. Proof:
   existing structure, apply the new `rexec_triple_addr` with the premises.
2. **Table construction:**
   ```coq
   Fixpoint table_of_list {Σ} (p : Term Σ ty_xlenbits) (off : N) (is : list AST)
     : list (Term Σ ty_xlenbits * AST) :=
     (* key k := peval_bvadd (term_val (bv.of_N (off + 4k))) p — construct
        THROUGH peval_bvadd so keys are born canonical: for p = term_val b
        they fold to literals; for symbolic p, constant-first sums; offset 0
        collapses to p itself via the zero rule. *)
   ```
   Exit table default: `[peval_bvadd (term_val (bv.of_N (4·len))) p]`
   (fall-through).
3. **Faithfulness discharge lemma** (once and for all):
   `inst p ι = SyncVal cbase → (bv.bin cbase + 4·len ≤ 1024) →
    faithful (table_of_list p 0 is) (instrs_of_list cbase is)` — induction on
   `is`, value-level bv arithmetic, reuse `instrs_of_list_fresh`. Exit analog
   against `pcOutOfInstrs_exitCond` (needs the same no-wrap bound; `ugeb`
   reflexivity at `cbase + 4len`).
4. **Contract layer:** `CFGVerifierContract`/`CFG_VC_triple`/`gen_contract`
   take the placement term `p` (concrete contracts pass
   `term_val (bv.of_N init_addr)` — same code path). Parameterized contracts
   use Σ extended with `"p"∷ty_xlenbits`; precondition gains
   `a = p` (formula_relop eq) and the fetch bound
   (`unsigned p + 4·len ≤ 1024` in the `ty.int` form the probe showed).
5. `cfg_instrs_*` / `cfg_instrs_endToEnd(_with_memory)` /
   `gen_contract_noninterferent`: valuation now supplies `p ↦ SyncVal
   (bv.of_N init_addr)`; add the bound hypothesis; memory lemmas
   (`instrsMemory`, `instrsAndDataMemory`, `mem_has_instrs`) already take a
   start address — unchanged.

---

## 5. Phase 4 — Examples and the headline theorem

**Model:** Sonnet for re-runs; Opus for the new symbolic-base VC if solve_vc
needs iteration. **Gate:** all existing `<prog>_noninterferent` lemmas green;
new parameterized lemma axiom-clean (`Print Assumptions` → "Closed under the
global context"; note the module-qualifier quirk).

1. Re-verify all existing examples (swap, jumpIfZero, jmp_fwd, countdown,
   countdown_mem, set_X2_to_42, cmovznz4, cmovznz4_at_start) through the new
   contract shape with concrete `p`. VCs should compute as before.
2. **Milestone:** `valid_cmovznz4_cfg_contract_param` — Σ = ["p"], symbolic
   placement, `vm_compute. solve_vc.` with the Phase-0 helpers. Then
   `cmovznz4_noninterferent_param : ∀ init_addr, (bound) →
   noninterferent_strong init_addr …` via the updated
   `gen_contract_noninterferent`.
3. Start with `set_X2_to_42` (2 instrs) as the cheap canary before cmovznz4.

---

## 6. Phase 5 — Docs and cleanup

Update CLAUDE.md (executor signature, table API, new pitfalls found en route),
memory (`project-cfgver-symbolic-base-spike` → completion status), commit with
`WIP (LLM):` prefixes and `Co-Authored-By` per convention. Remove the now-dead
`term_get_val` guard comments and `instrAligned` if still vestigial.

---

## 7. Residual risks (ranked) and what to do if they fire

1. **rsolve/RefineCompat plumbing for table-carrying sexec** — expect missing
   instances; `Set Typeclasses Debug.`, add `#[export] Instance`s. If the
   angelic_binary/refine_bind skeleton fights the premises, fall back to
   manual `iApply` chains as in the current proof.
2. **World-stability packaging of faithfulness** — if
   `forgetting_unconditionally_drastic` won't project the hypotheses, restate
   them as plain Coq `Prop` hypotheses outside the entailment (they only
   mention `inst`/`ι`) and re-introduce per world via `faithful_persist`.
3. **Unforeseen solver substitutions denormalizing terms mid-VC** — symptom:
   `lookup_instr` returns None on a pc that "should" match; the VC errors
   loudly (by design). Diagnose by `vm_compute`-printing the postprocessed
   tree and comparing the pc term against the peval'd keys. Fix belongs in
   `lookup_instr`'s normalization, never in the solver.
4. **Bounds obligations in shapes the Phase-0 helpers miss** — extend the
   helper set; they are all linear facts under `bv.bin` with small constants.
5. If any step seems to require solver-level bvadd cancellation or
   enumerating the table per step — **stop; the design is being violated;
   report back** (see decision 5 and the rejected-alternatives list).

## 8. Workflow reminders (from CLAUDE.md — they bite)

- rocq-mcp over raw coqc; `keep_vo=True` on Verifier.v before compiling
  Examples.v; `mode=vos` for statement iteration, `mode=full` for proofs.
- `rocq_start(theorem=X)` loads the prefix WITHOUT running proofs — a
  successful start proves nothing about earlier lemmas.
- Bullet discipline in iInduction proofs: `-` top, `+` angelic, `--`
  refine_bind, `*` lookup cases.
- `Makefile.coq` must be regenerated if `_CoqProject` changed
  (`rm Makefile.coq && make Makefile.coq`).
