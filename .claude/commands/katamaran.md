# Katamaran deep-dive reference

This skill gives detailed context about the Katamaran project. Read the user's
current question/task and provide the relevant portion below as context, then continue
with whatever they asked for.

---

## Project dependencies

```
Spec.vo ← Verifier.vo ← Examples.vo ← EndToEnd.vo
                              ↑
               also imports BlockVer.Verifier
```

When modifying Verifier.v: recompile with `keep_vo=True` before compiling Examples.v.

---

## The RefineCompat / rsolve system

### What it does
`rsolve` proves goals of the form:
```
RefineCompat RProp (cexec_foo arg1 ... argn) w (sexec_foo arg1 ... argn w) inst
```
i.e. "the concrete executor refines the symbolic executor".

### How to add a new instance
```coq
#[export] Instance refine_compat_my_thing {Σ : LCtx} (params...) {w} :
    RefineCompat (LogicalSoundness.RProp)
      (cconcrete_thing params) w (ssymbolic_thing params w) _ :=
    MkRefineCompat (rmy_thing params).
```
Where `rmy_thing` is the relational correctness lemma proved separately.

### Debugging rsolve
```coq
Set Typeclasses Debug.  (* shows search tree *)
(* Then run: *)
rsolve.
(* Look for "trying instance" failures — add the missing RefineCompat instance *)
```

### `rexec_cfg_addr` bullet nesting
The relational lemma for the CFG executor uses `iInduction fuel`. Inside the
`S n'` bullet (`-`), the angelic_binary creates sub-goals that MUST use `+` bullets:

```coq
- rsolve.           (* fuel = 0 *)
- rsolve.           (* fuel = S n', intro step *)
  destruct (term_get_val_spec ta) ...
  rsolve.
  + destruct (exitCond v); rsolve.          (* angelic_binary sub-goals *)
  + destruct (instrAligned v).
    2: rsolve.
    destruct (List.nth_error b _) as [i|].
    * iApply (refine_bind ...).             (* nth_error = Some *)
      -- now iApply (rexec_instruction i ...).
      -- rsolve. iPoseProof (forgetting_unconditionally_drastic ...).
         iApply ("IH" with "[$]").
    * rsolve.                               (* nth_error = None *)
```

---

## CFGVer soundness: what exists vs what's missing

### Exists (in Verifier.v)
- `sexec_cfg_addr` / `cexec_cfg_addr` (symbolic/concrete CFG executor)
- `rexec_cfg_addr` (relational correctness)
- `sound_exec_cfg_addr` (soundness, gives WP2_loop)
- `sound_cexec_triple_addr` (full triple soundness → semTripleCFG)
- `sound_sblock_verification_condition` (VC → semTripleCFG)
- `refine_compat_block_verification_condition` (rsolve instance)

### Exists (in Examples.v)
- `valid_jmp_fwd_cfg_vc` / `valid_jmp_fwd_cfg` (proved, commit 90f65ba8)
- `myWP2_loop` / `myWP2_loop_fix` / `fixpoint_myWP2_loop_eq`
- `exitCondImpliesMyWP2_loop`
- `myWP2_loop_semTriple` / `myWP2_loop_semTripleBlock`
- `adequacy_gen_RiscVNStepsExitCond` (needs myWP2_loop as input)
- `sound_exec_instruction` / `sound_exec_block_addr` (BlockVer)

### Missing (needed for CFGVer end-to-end)
- `sound_exec_cfg_addr_myWP2` — KEY MISSING LEMMA
  Signature:
  ```coq
  Lemma sound_exec_cfg_addr_myWP2 `{sailGS2 Σ}
      {b exitCond fuel} (apc : RelVal ty_xlenbits)
      (ExitCondIprop : iProp Σ) Φ (h : SCHeap) :
    cexec_cfg_addr b exitCond fuel apc Φ h →
    interpret_scheap h ∗ pc ↦ᵣ apc ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs (SyncVal bv.zero) b ⊢
    (∀ an,
       ⌜match an with SyncVal v => exitCond v = true | NonSyncVal _ _ => True end⌝ ∗
       pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs (SyncVal bv.zero) b ∗
       (∃ h', interpret_scheap h' ∧ ⌜Φ an h'⌝) -∗ ExitCondIprop) -∗
    myWP2_loop ExitCondIprop.
  ```
  Proof strategy: induction on `fuel`.
  - fuel = 0: CHeapSpec.error, so `Φ` is `False`, contradiction.
  - fuel = S n', apc = SyncVal v:
    - angelic choice: exit branch → `exitCond v = true` → call continuation → ExitCondIprop
      → `exitCondImpliesMyWP2_loop`.
    - continue branch → execute one instruction via `sound_exec_instruction`
      → `myWP2_loop_semTriple` unfolds one myWP2_loop step → IH.
  - fuel = S n', apc = NonSyncVal: treat as "exit" (continuation called directly).

- `sound_cexec_triple_addr_myWP2` — builds on above
- `jmp_fwd_safe_cfg` — the concrete pre → myWP2_loop wrapper
- `jmp_fwd_endToEnd_cfg` — top-level leakage-equivalence statement

---

## WP2_loop vs myWP2_loop

This is a fundamental distinction that caused confusion:

```
WP2_loop         = fixpoint (λ wp, semWP2 fun_loop fun_loop ... ▷ wp)
myWP2_loop ExitC = fixpoint (λ wp, ExitC ∨ semWP2 fun_step fun_step ... ▷ wp)
```

`WP2_loop ⊢ myWP2_loop ExitC` is TRUE (by Löb: always take the Right branch),
but USELESS for adequacy — the adequacy proof needs the Left branch (ExitC) to
fire at the right time.

The bridge `sound_exec_cfg_addr_myWP2` constructs `myWP2_loop` step-by-step so the
Left branch fires exactly when `exitCond` holds.

---

## Key imports pattern (Examples.v)

```coq
(* In Section AdequacyTools — needed for myWP2_loop bridge lemma: *)
Import Katamaran.RiscvPmp.CFGVer.Verifier  (* qualified, NOT Import *)

(* Access as: *)
Katamaran.RiscvPmp.CFGVer.Verifier.cexec_cfg_addr
Katamaran.RiscvPmp.CFGVer.Verifier.sblock_verification_condition (Σ := [ctx]) ...
```

---

## Assertions in CFGVer

| Context | Type |
|---------|------|
| Precondition `req` | `Assertion (Σ ▻ "a"∷ty_xlenbits)` |
| Postcondition `ens` | `Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits)` |

`asn_init_pc = (term_var "a" = term_val ty_xlenbits bv.zero)` — asserts start PC = 0.
`asn_next_pc_eq t = (term_var "an" = t)` — asserts final PC = t.
Both defined in `Section WithAsnNotations` of `Examples.v`.

For `sblock_verification_condition`, `Σ` must be provided explicitly as `[ctx]`
when no extra logical variables are needed.

---

## solve_vc residual patterns

After `vm_compute`, typical residuals and their solutions:

| Residual | Solution |
|----------|----------|
| `VerificationConditionWithErasure (Erasure.eformula_secLeak [bv 0x0] ∧ ⊤)` | `solve_vc.` |
| `VerificationConditionWithErasure ⊤` | `constructor.` |
| `VerificationConditionWithErasure False` | wrong VC — check exitCond or postcondition |

`solve_vc` is from `RiscvPmpBlockVerifExecutor` (imported globally in Examples.v).

---

## Commit conventions

All LLM-generated commits use the message format:
```
WIP (LLM): <description>

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>
```

---

## Proof workflow: avoid pre-reading, let Coq guide you

**Anti-pattern (wastes tokens):** Reading `semTriple`, `consume_sound`,
`own_regstore2`, `instrs_endToEnd`, etc. upfront trying to analytically predict
what every proof will need before writing any code. This burns hundreds of tokens
on exploration that may be irrelevant.

**Correct pattern:**
1. Draft the proof based on the known analogue (e.g. `swap_endToEnd` for a new
   end-to-end lemma, `sound_cexec_triple_addr` for a new soundness wrapper).
2. Compile with `rocq_compile_file mode="vos"` immediately.
3. Read the error message. It tells you exactly what's missing (wrong type,
   missing hypothesis, wrong resource) in one shot.
4. Fix that specific thing and repeat.

One compile-and-fix cycle costs ~2 tool calls. Extensive pre-reading to avoid
that cycle costs 20+ tool calls and usually still misses something.

**Corollary:** never read a definition just to understand it — only read it
when a specific error message points you there. Trust that the proof analogue
is structurally correct and let Coq reject what isn't.

**When a user hint is ambiguous:** ask for clarification immediately rather
than spending tokens researching to resolve the ambiguity yourself. One
clarifying question costs nothing; 20 exploratory reads costs the whole budget.
Example: "jmp_fwd will need some public registers" — just ask "which register(s)
specifically?" instead of reading `own_regstore2`, `instrs_endToEnd`, etc.

---

## Updating this skill

To update: edit `.claude/commands/katamaran.md` directly. Add new sections as the
project evolves. Key triggers for updates:
- New lemmas proved in CFGVer soundness chain
- New pitfalls encountered
- Changes to module structure or import strategy
