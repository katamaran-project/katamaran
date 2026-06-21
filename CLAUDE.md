# Katamaran — Claude Code Project Guide

Katamaran is a Rocq/Coq framework for formal security verification of RISC-V PMP programs.
The active development area is `case_study/RiscvPmp/CFGVer/`.

---

## Project layout

| Path | Logical name | Purpose |
|------|-------------|---------|
| `case_study/RiscvPmp/` | `Katamaran.RiscvPmp` | RISC-V PMP case study |
| `case_study/RiscvPmp/BlockVer/` | `…BlockVer` | Linear (block) verifier |
| `case_study/RiscvPmp/CFGVer/` | `…CFGVer` | CFG verifier (active work) |
| `theories/` | `Katamaran` | Core framework |

`_CoqProject` defines the `-Q` mappings and the exact compilation order.
CFGVer compilation order: `Spec.v` → `Verifier.v` → `Examples.v` → `EndToEnd.v`.

---

## rocq-mcp workflow

Always prefer rocq-mcp tools over spawning `coqc` manually.

`ROCQ_MAX_STATES` is **not** overridden — the server uses its default limit.
Consequence: interactive sessions (`rocq_start`) may expire if idle or if many
states accumulate. Always save the `state_id` from `rocq_start` and check for
`state not found` errors before assuming a session is still live; restart with
`rocq_start` if needed.

```
# 1. Fast type-check (skips proof bodies) — use first
rocq_compile_file(file, mode="vos")

# 2. Full compile — use to validate proofs
rocq_compile_file(file, mode="full")

# 3. Keep .vo so downstream files can Require it
rocq_compile_file(file, mode="full", keep_vo=True)

# 4. Interactive proof development
s = rocq_start(file=..., theorem="my_lemma")
s = rocq_check(from_state=s["state_id"], body="intros. iIntros ...")
```

**Dependency rule**: if `Examples.v` does `Require RiscvPmp.CFGVer.Verifier`, compile
`Verifier.v` with `keep_vo=True` first, then compile `Examples.v`.

**VOS vs full**: use `vos` to catch statement errors cheaply; use `full` only when
the proof body matters. VOS does NOT check `Proof.…Qed.`.

---

## Essential Rocq debugging commands

Paste these at the top of a `rocq_check` body when goals are confusing:

```coq
Unset Printing Notations.    (* see raw terms instead of notation *)
Set Printing Implicit.       (* show implicit arguments *)
Set Printing All.            (* show everything; very verbose *)
Set Typeclasses Debug.       (* trace typeclass search — invaluable for rsolve failures *)
```

Reset with the `Un/Set` inverse. Use `Print refine_compat_block_verification_condition.`
to inspect specific instances.

---

## CFGVer key definitions

### `sexec_cfg_addr` / `cexec_cfg_addr`

Symbolic/concrete CFG executor. Signature:

```coq
sexec_cfg_addr (b : list AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
  : ⊢ STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits)
```

At each step: `angelic_binary` (existential choice) between exiting and executing
the next instruction. `angelic_binary m1 m2 Φ h = m1 Φ h \/ m2 Φ h`.

Stops with `error` when:
- `fuel = 0`
- `term_get_val apc = None` (symbolic, non-concrete address)
- `instrAligned v = false`
- `nth_error b idx = None` (out of bounds)

### `instrAligned`

```coq
Definition instrAligned (v : bv xlenbits) : bool :=
  (N.to_nat (bv.bin v) mod bytes_per_instr =? 0)%nat.
#[global] Arguments instrAligned : simpl never.
```

### `semTripleCFG`

```coq
Definition semTripleCFG PRE instrs exitCond fuel POST : iProp Σ :=
  (∀ a,
     (PRE a ∗ pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs (SyncVal bv.zero) instrs) -∗
     (∀ an, ⌜match an with SyncVal v => exitCond v = true | NonSyncVal _ _ => True end⌝ ∗
            pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs (SyncVal bv.zero) instrs ∗ POST a an
            -∗ WP2_loop) -∗
     WP2_loop)%I.
```

`WP2_loop` here is `BlockVer.Verifier.WP2_loop` (plain infinite loop, NOT
`myWP2_loop ExitCondIprop`). Bridging to `myWP2_loop` is the key open problem.

### `sblock_verification_condition` (CFGVer)

```coq
sblock_verification_condition {Σ : LCtx}
  (req : Assertion (Σ ▻ "a"∷ty_xlenbits))
  (b : list AST)
  (exitCond : bv xlenbits -> bool)
  (fuel : nat)
  (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
  (w : World) : 𝕊 w
```

Call pattern: `sblock_verification_condition (Σ := [ctx]) req b exitCond fuel ens wnil`.
`Σ := [ctx]` must be explicit — Coq cannot infer it.

**Note on postconditions**: `SHeapSpec` has no leakcheck — resources left in the
heap after consuming `ens` are silently dropped. `CFGVerifierContract` therefore
does NOT expose a postcondition field; `CFG_VC_triple` internally uses the trivially-
true assertion `asn.formula (formula_bool (term_val ty.bool true))` as `ens`.
`sound_cexec_triple_addr_myWP2` and `sound_sblock_verification_condition_myWP2`
keep `post` as an implicit hypothesis parameter (for generality) but do NOT pass
`asn.interpret post ...` to the caller's continuation — the final heap is simply
discarded (affinely dropped in Iris).

---

## RefineCompat / rsolve infrastructure

`rsolve` tactic automatically closes relational goals between symbolic and concrete.
Driven by `RefineCompat` typeclass instances:

```coq
Class RefineCompat (R : 𝕊 w -> C -> Prop) (c : C) (w : World) (s : 𝕊 w) ... :=
  MkRefineCompat { refine_compat : R s c }.
```

Key instances in `CFGVer/Verifier.v`:
- `refine_compat_angelic_binary` — handles `angelic_binary`
- `refine_compat_block_verification_condition` — handles the full VC

When `rsolve` fails: `Set Typeclasses Debug.` and look for the missing `RefineCompat`
instance. Usually the fix is to add one `#[export] Instance`.

`rexec_cfg_addr`: the relational correctness lemma for `sexec_cfg_addr`. Proved by
`iInduction fuel`. **Bullet nesting rule**: inside `-` bullets from `iInduction`, use
`+` for angelic_binary sub-goals, `--` for refine_bind sub-goals, `*` for nth_error cases.

---

## Soundness chain (CFGVer)

The `jmp_fwd_endToEnd_cfg` end-to-end proof is **complete** (commit `fe149069`).
The chain for `jmp_fwd` is:

```
valid_jmp_fwd_cfg_vc        (vm_compute. solve_vc.)
        ↓  safeE (postprocess (sblock_verification_condition ...))
sound_sblock_verification_condition_myWP2
        ↓  → myWP2_loop ExitCondIprop
jmp_fwd_safe_cfg / cfg_instrs_contract
        ↓  → exitCond_WP2_loop jmp_fwd_exitCond
cfg_instrs_endToEnd
        ↓  adequacy_gen_RiscVNStepsExitCond + memory boilerplate
        → concrete leakage equivalence
```

`sound_sblock_verification_condition_myWP2` (in `Examples.v`) bridges directly
from VC soundness to `myWP2_loop`, bypassing the `semTripleCFG → WP2_loop` step.

For other programs, there is still a potential open problem:
```
semTripleCFG PRE b exitCond fuel POST  → WP2_loop
[potentially needed] sound_exec_cfg_addr_myWP2
        ↓  → myWP2_loop ExitCondIprop
```

**BlockVer end-to-end chain** (works, see `swap_endToEnd`):
```
safeE (postprocess (sblock_verification_condition req instrs ens wnil))
  → sound_sblock_verification_condition → semTripleBlock
  → myWP2_loop_semTripleBlock → myWP2_loop ExitCondIprop
  → instrs_endToEnd
  → adequacy_gen_RiscVNStepsExitCond → leakage equivalence
```

---

## Contract generator (`gen_contract`)

Defined in `Examples.v` inside `WithAsnNotations`. Automates building
`CFGVerifierContract` from a list of register specs and provides a
once-and-for-all `ImplPre` lemma.

### Types and definitions

```coq
Definition reg_spec : Type := RegIdx * bool.   (* (register, is_public) *)

(* Assertion for one spec: existential over a RelVal, with secLeak if public *)
Definition gen_reg_asn {Σ} (s : reg_spec) : Assertion Σ :=
  let '(r, is_pub) := s in
  asn.exist "v" ty_xlenbits
    (if is_pub then r ↦ᵣ term_var "v" ∗ secLeakvar "v"
               else r ↦ᵣ term_var "v").

(* Precondition: fold with ∗; gen_pre [] = ⊤ *)
Definition gen_pre {Σ} (specs : list reg_spec) : Assertion Σ :=
  List.fold_right (fun s acc => gen_reg_asn s ∗ acc) ⊤ specs.

(* Contract: precondition is asn_init_pc ∗ gen_pre specs *)
Definition gen_contract (specs : list reg_spec) (instrs : list AST)
    (ec : bv xlenbits -> bool) (fl : nat) : CFGVerifierContract :=
  @MkCFGVerifierContract [ctx] (asn_init_pc ∗ gen_pre specs) instrs ec fl.

(* Public register list: entries with is_public = true, converted to Reg *)
Definition gen_public_regs (specs : list reg_spec) : list {x : Ty & 𝑹𝑬𝑮 x} :=
  base.omap (fun '(r, pub) =>
    if pub then option_map (@existT Ty 𝑹𝑬𝑮 ty_xlenbits) (reg_convert r)
    else None) specs.
```

### `gen_implpre` — once-and-for-all `ImplPre`

```coq
Lemma gen_implpre `{sailGS2 Σ}
    (specs : list reg_spec) (γ1 γ2 : RegStore)
    (ι : Valuation ([ctx] ▻ "a"∷ty_xlenbits))
    (HpubReg : declare_public_registers γ1 γ2 (gen_public_regs specs))
    (HND : NoDup (map fst specs)) :
  interp_gprs_with_public_registers γ1 γ2 (gen_public_regs specs) ⊢
  asn.interpret (gen_pre specs) ι.
```

Converts Iris register ownership into the symbolic `gen_pre` assertion. For
public registers it uses `regPstsTo_sync_is_nonsync` to unify `NonSyncVal v v`
into `SyncVal v`. `gen_implpre` for `specs = []` is trivially `True ⊢ True`.

### Helper lemmas

```coq
Lemma declare_pub_head_true r x rest γ1 γ2 :
  reg_convert r = Some x →
  declare_public_registers γ1 γ2 (gen_public_regs ((r, true) :: rest)) →
  read_register γ1 x = read_register γ2 x.
(* Note: x is implicit under Set Implicit Arguments — use eapply, not exact *)

Lemma declare_pub_tail r pub rest γ1 γ2 :
  declare_public_registers γ1 γ2 (gen_public_regs ((r, pub) :: rest)) →
  declare_public_registers γ1 γ2 (gen_public_regs rest).
```

---

## `cfg_instrs_endToEnd` (CFGVer generic end-to-end)

CFG analog of BlockVer's `instrs_endToEnd`. Bundles adequacy +
memory splitting + `cfg_instrs_safe` so that program-specific proofs
only supply `ImplPre`.

```coq
Lemma cfg_instrs_endToEnd {γ1 γ2 γ1' γ2' : RegStore} {μ1 μ2 μ1' μ2' : Memory}
  instrs' exitCond n ws {R} {ι : Valuation R}
  public_registers
  (HpubReg : declare_public_registers γ1 γ2 public_registers)
  (block : @CFGVerifierContract R)
  (valid_block : ValidCFGVerifierContract block)
  (blockInstrs : cfg_instrs block = instrs')
  (blockExitCond : cfg_exitCond block = exitCond)
  (ImplPre : forall `{sailGS2 Σ},
      interp_gprs_with_public_registers γ1 γ2 public_registers ∗
      cur_privilege ↦ᵣ ty.SyncVal Machine ∗
      interp_inv_constant_time -∗
      asn.interpret (extend_to_minimal_pre (cfg_precondition block))
        ι.["a"∷ty_xlenbits ↦ SyncVal (bv.of_N init_addr)]) :
  (4 * N.of_nat (length instrs') < lenAddr)%N ->
  mem_has_instrs μ1 (bv.of_N init_addr) ws instrs' ->
  mem_has_instrs μ2 (bv.of_N init_addr) ws instrs' ->
  RiscvPmpProgram.read_register γ1 cur_privilege = Machine ->
  RiscvPmpProgram.read_register γ2 cur_privilege = Machine ->
  RiscvPmpProgram.read_register γ1 pc = bv.of_N init_addr ->
  RiscvPmpProgram.read_register γ2 pc = bv.of_N init_addr ->
  ⟨ γ1, μ1 ⟩ -(exitCond, n)->* ⟨ γ1', μ1' ⟩ ->
  ⟨ γ2, μ2 ⟩ -(exitCond, n)->* ⟨ γ2', μ2' ⟩ ->
  leakage_trace μ1 = leakage_trace μ2 ->
  leakage_trace μ1' = leakage_trace μ2'.
```

No `ImplPost` parameter — postconditions were removed from `CFGVerifierContract`.

**Call pattern** (from `jmp_fwd_endToEnd_cfg`):

```coq
eapply (@cfg_instrs_endToEnd γ1 γ2 γ1' γ2' μ1 μ2 μ1' μ2'
  instrs jmp_fwd_exitCond n ws [ctx] [env]
  [existT ty_xlenbits x1] HpubReg jmp_fwd_cfg_contract
  valid_jmp_fwd_cfg_contract eq_refl eq_refl).
all: try eauto.
```

`@` is required because `Set Implicit Arguments.` makes `instrs'` and `exitCond`
implicit (they appear in the types of `blockInstrs`/`blockExitCond`).

**`all: try eauto.` must come BEFORE the `-` bullets** — it handles routine
goals (memory, register reads, execution steps) first, leaving only `ImplPre`
and the length bound for the focused bullets.

**Proof body pattern** (inside `cfg_instrs_endToEnd`'s own proof):

```coq
iApply (cfg_instrs_safe γ1 γ2 block).
all: eauto.
iIntros "(Hregs & Hpriv & #Hinv')".
iApply ImplPre.          (* NOT iApply (ImplPre Σ') — Σ is implicit, inferred *)
iFrame "∗ #".
by iFrame "∗ #".         (* second iFrame closes the residual after the first *)
```

### `ImplPre` proof pattern for `gen_contract`

When `block = gen_contract specs`, the goal after `cbn` is a pair of
`⌜P⌝ ∧ emp` fragments (one for `asn_init_pc`, one for `gen_pre specs`)
followed by `cur_privilege` and `interp_inv_constant_time`.

**Empty specs** (`gen_contract []`, see `jmp_fwd_endToEnd_cfg_gen`):

```coq
assert (HpubReg : declare_public_registers γ1 γ2 []) by constructor.
eapply (@cfg_instrs_endToEnd ... [] HpubReg jmp_fwd_cfg_contract_gen
  valid_jmp_fwd_cfg_contract_gen eq_refl eq_refl).
all: try eauto.
- intros Σ H.
  iIntros "(Hregs & Hpriv & #Hinv)".
  cbn. iFrame "∗ #".                        (* frames Hpriv and Hinv *)
  iSplit; (iSplit; [iPureIntro | done]).    (* decompose ⌜P⌝ ∧ emp for each fragment *)
  all: vm_compute; done.                   (* closes init_addr=0 and True *)
- cbn. by unfold lenAddr.
```

**`declare_public_registers γ1 γ2 []`** is proved by `by constructor` (stdpp's
`Forall_nil` is an iff lemma, not the constructor — do NOT use `Forall_nil _`).

---

## Public memory infrastructure

Analogous to the public-register machinery, for programs that also access data memory.

### Types and definitions (all in `CFGVer/Examples.v`)

```coq
(* mem_spec: (word-address, is_public) *)
Definition mem_spec : Type := Val ty_word * bool.

(* Prop: μ1 and μ2 agree on every address in the public subset of specs *)
Definition declare_public_memory (μ1 μ2 : Memory) (addrs : list (Val ty_word)) : Prop :=
  Forall (fun a => get_word μ1 a = get_word μ2 a) addrs.

(* The public addresses from a spec list *)
Definition gen_public_addrs (specs : list mem_spec) : list (Val ty_word) :=
  base.omap (fun '(a, pub) => if pub then Some a else None) specs.

(* Two-world memory ownership — all entries as NonSyncVal (raw form) *)
Definition interp_mem_with_memory `{sailGS2 Σ} (μ1 μ2 : Memory)
    (specs : list mem_spec) : iProp Σ :=
  [∗ list] spec ∈ specs,
    let '(a, _) := spec in
    interp_ptstomem (width := 4) (SyncVal a)
      (NonSyncVal (get_word μ1 a) (get_word μ2 a)).

(* Two-world memory ownership — public entries as SyncVal, private as NonSyncVal *)
Definition interp_mem_with_public_memory `{sailGS2 Σ} (μ1 μ2 : Memory)
    (specs : list mem_spec) : iProp Σ :=
  [∗ list] spec ∈ specs,
    let '(a, pub) := (spec : mem_spec) in
    if pub
    then interp_ptstomem (width := 4) (SyncVal a) (SyncVal (get_word μ1 a))
    else interp_ptstomem (width := 4) (SyncVal a)
           (NonSyncVal (get_word μ1 a) (get_word μ2 a)).
```

### `something_memory` equivalence

```coq
Lemma something_memory `{sailGS2 Σ} μ1 μ2 (specs : list mem_spec)
    (HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs specs)) :
  interp_mem_with_memory μ1 μ2 specs ⊣⊢
  interp_mem_with_public_memory μ1 μ2 specs.
```

Usage: `rewrite (something_memory data_specs HpubMem)` rewrites `interp_mem_with_memory`
to `interp_mem_with_public_memory` in the current Iris proof state (including hypothesis
types, since Iris environments are Coq terms).

### `instrsAndDataMemory` (Admitted)

Extracts `ptsto_instrs ∗ interp_mem_with_memory` from the raw `mem_res2_without_leak`.
Data words must occupy the `4*|data_specs|` bytes immediately following the instruction
region. The proof is structurally analogous to `instrsMemory` but requires a 3-way
`bv.seqBv_app` split and induction over `data_specs`.

```coq
Lemma instrsAndDataMemory `{sailGS2 Σ} {μ1 μ2} ws_instrs data_specs instrs :
  (4 * N.of_nat (length instrs) + 4 * N.of_nat (length data_specs) < lenAddr)%N →
  mem_has_instrs μ1 (bv.of_N init_addr) ws_instrs instrs →
  mem_has_instrs μ2 (bv.of_N init_addr) ws_instrs instrs →
  (∀ i spec, data_specs !! i = Some spec →
    spec.1 = bv.of_N (init_addr + 4 * N.of_nat (length instrs) + 4 * N.of_nat i)) →
  mem_res2_without_leak μ1 μ2 ⊢ |={⊤}=>
    ptsto_instrs (SyncVal (bv.of_N init_addr)) instrs ∗
    interp_mem_with_memory μ1 μ2 data_specs.
Proof. Admitted.
```

### `cfg_instrs_verified_with_mem` / `cfg_instrs_safe_with_mem`

Memory-aware variants of `cfg_instrs_verified` / `cfg_instrs_safe`. The `ImplPre`
parameter also receives `interp_mem_with_public_memory μ1 μ2 data_specs`.

**Call pattern** for `cfg_instrs_safe_with_mem` in `cfg_instrs_endToEnd_with_memory`:
```coq
iApply (cfg_instrs_safe_with_mem γ1 γ2 data_specs μ1 μ2 block).
all: eauto.
iIntros "(Hregs & Hmem & Hpriv & #Hinv')".
iApply ImplPre.
rewrite <- (something_registers HpubReg).
iFrame "Hmem ∗ #".
by iFrame "∗ #".
```

`Set Implicit Arguments` makes `data_specs, μ1, μ2` implicit in `cfg_instrs_verified_with_mem`
(first explicit = `γ1 : RegStore`) but explicit in `cfg_instrs_safe_with_mem` (explicit: `γ1, γ2,
data_specs, μ1, μ2, block`).

### `cfg_instrs_endToEnd_with_memory`

Extension of `cfg_instrs_endToEnd` for programs with data memory. Requires:
- `data_specs : list mem_spec`
- `HpubMem : declare_public_memory μ1 μ2 (gen_public_addrs data_specs)`
- `HDataAddrs` mapping spec indices to concrete addresses (contiguous after instruction region)
- `ImplPre` now also takes `interp_mem_with_public_memory μ1 μ2 data_specs`

The length bound is `4 * |instrs| + 4 * |data_specs| < lenAddr` (combined).

`instrsAndDataMemory` is Admitted — the statement is correct but the proof needs the
`bv.seqBv_app` split and an induction over `data_specs` (not yet written).

---

## Common pitfalls

| Symptom | Fix |
|---------|-----|
| `Cannot find a physical path bound to…CFGVer.Verifier` | Compile `Verifier.v` with `keep_vo=True` first |
| `Cannot infer the implicit parameter Σ` | Add `(Σ := [ctx])` to `sblock_verification_condition` |
| `Wrong bullet -: Current bullet - is not finished` | Inner bullets inside `iInduction` must use `+`/`--`/`*`, not `-` |
| `No such goal` after `iFrame` | `iFrame` closes `True` goals automatically; remove the trailing `done.` |
| `Cannot infer exitCond` in `apply sound_sblock_verification_condition` | Use `apply (sound_cexec_triple_addr exitCond)` explicitly |
| `rsolve` hangs or fails | Add `Set Typeclasses Debug.`; likely a missing `RefineCompat` instance |
| `From Katamaran Require Import CFGVer.Verifier` causes name clashes | Use `Require` (no Import) and qualified names: `Katamaran.RiscvPmp.CFGVer.Verifier.foo` |
| `iApply`/`iExact` fails despite terms being "equal" | `Is_true b` (Rocq's `Bool.Is_true`) is NOT definitionally equal to `b = true`; Iris tactics use syntactic matching. Convert with `cbn; rewrite Hexit; exact I` or ensure both sides use the same form. |
| `iApply H` fails with "cannot apply (cfg_instrs_contract ...)" | Iris doesn't auto-unfold opaque-looking Definitions to find wand structure. Use `unfold cfg_instrs_contract, exitCond_WP2_loop.` before applying, or use `iPoseProof ... as "H"` first. |
| `exitCond_WP2_loop` uses `= true` but adequacy goal has `∨ bool` | `exitCond_WP2_loop` must use `⌜exitCond v ∨ exitCond v'⌝` (Is_true coercion), matching `adequacy_gen_RiscVNStepsExitCond`'s form and `pcOutOfInstrs_WP2_loop`. |
| `iApply (jmp_fwd_safe_cfg ...)` on `\|={⊤}=>` goal leaves `\|={⊤}=> True` subgoal | Iris applies through the fancy-update but leaves a trivial side condition; close with `done.` |
| `iApply (ImplPre Σ')` gives "expected gFunctors" | `Σ` is explicit in `forall \`{sailGS2 Σ}`; use `iApply ImplPre.` (no arg) and let Coq infer `Σ` from the ambient Iris context. |
| `Wrong bullet -: Current bullet - is not finished` after `iApply ImplPre` | Missing second `iFrame`; use `iFrame "∗ #". by iFrame "∗ #".` — the second call closes the residual `interp_gprs` goal. |
| `eapply cfg_instrs_endToEnd instrs exitCond ...` gives type mismatch | `Set Implicit Arguments.` makes `instrs'` and `exitCond` implicit; use `@cfg_instrs_endToEnd` with all args explicit. |
| `declare_public_registers γ1 γ2 []` proof fails with `Forall_nil _` | `Forall_nil` in stdpp is an iff lemma (`Forall P [] ↔ True`), not the constructor. Use `by constructor` instead. |
| `declare_pub_head_true r x rest ...` gives type mismatch for `x` | `Set Implicit Arguments` makes `x : Reg ty_xlenbits` implicit. Use `by eapply declare_pub_head_true` and let Coq infer `x` from `Hrc`. |
| `bv.finite.all_spec` not found | The lemma is `bv.finite.elem_of_enum : ∀ [m] (x : bv m), x ∈ bv.finite.enum m`. Use `apply elem_of_list_to_set, bv.finite.elem_of_enum.` |
| `rewrite (something_registers HpubReg)` fails with "does not match any subterm" | The LHS is `interp_gprs_with_registers`; if the goal already has `interp_gprs_with_public_registers`, rewrite the other way: `rewrite <- (something_registers HpubReg)`. |
| `all: vm_compute; done.` inside a `-` bullet closes too many goals | It is scoped to the current bullet's sub-goals. If it unexpectedly closes outer goals, ensure `all: try eauto.` runs FIRST (before the `-` bullets) to discharge the routine goals. |
| `iApply (cfg_instrs_safe_with_mem data_specs μ1 μ2)` — type mismatch (`data_specs` at `RegStore` position) | `Set Implicit Arguments` makes `data_specs, μ1, μ2` implicit (appear in `ImplPre`'s type); first explicit arg is `γ1 : RegStore`. Use `iApply (cfg_instrs_safe_with_mem γ1 γ2 data_specs μ1 μ2 block)`. |
| `iFrame "Hmemdata ∗ #"` fails with "Hmemdata not found" inside `ImplPre` subgoal | `cfg_instrs_safe`'s `ImplPre` starts with an empty Iris spatial context; outer hypotheses are invisible. Use `cfg_instrs_safe_with_mem` instead — it threads `interp_mem_with_public_memory` through as a conjunct in `ImplPre`'s domain. |

---

## Importing CFGVer.Verifier into Examples.v

```coq
(* At top level, after the main Require Import block: *)
From Katamaran Require
     RiscvPmp.CFGVer.Verifier.
```

Then use qualified: `Katamaran.RiscvPmp.CFGVer.Verifier.sblock_verification_condition`.
Do NOT `Require Import` — it causes notation/name conflicts with BlockVer.

---

## jmp_fwd example status

`valid_jmp_fwd` in `Section WithAsnNotations`: **Admitted** — BlockVer cannot handle
JAL (non-linear control flow).

`valid_jmp_fwd_cfg` / `valid_jmp_fwd_cfg_vc`: **Proved** (commit `90f65ba8`).
Uses CFGVer with `jmp_fwd_exitCond := fun v => bv.ugeb v (bv.of_N 8)`, fuel = 5.
Proof: `vm_compute. solve_vc.`

End-to-end (`jmp_fwd_endToEnd_cfg`): **Proved** (commit `fe149069`).
Manual contract, requires `declare_public_registers γ1 γ2 [existT ty_xlenbits x1]`.

**gen_contract version** (`jmp_fwd_cfg_contract_gen` / `jmp_fwd_endToEnd_cfg_gen`):
**Proved** (commit `63affd15`). Uses `gen_contract []` (empty specs, precondition
`asn_init_pc ∗ ⊤`). End-to-end requires no `HpubReg` hypothesis — proved by
`by constructor` for `declare_public_registers γ1 γ2 []`.

---

## Updating this file

This file should be updated whenever:
- A new lemma / definition pattern is discovered
- A common pitfall is encountered and resolved
- The soundness chain is extended
- New imports or module structure changes occur

Previous Claude sessions: commits tagged `WIP (LLM):` are primarily LLM-generated.
