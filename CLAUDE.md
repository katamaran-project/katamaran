# Katamaran — Claude Code Project Guide

Katamaran is a Rocq/Coq framework for formal security verification of RISC-V PMP programs.
The active development area is `case_study/RiscvPmp/CFGVer/`.

---

## Collaboration style

- **Report before acting.** Before any significant edit, proof attempt, or design
  decision, state in one sentence what I'm about to try and why — so the user can
  redirect before I commit.

- **Decision checkpoints.** When I hit a fork (e.g. "option A or B?"), stop and
  ask explicitly rather than pick one and run with it.

- **Surface intermediate findings.** During deep exploration, report what I've
  found every few steps rather than one large dump at the end.

- **Come back when stuck.** If I've been working on something for a while without
  clear progress, stop and report back — don't keep going silently. Say what I've
  tried, where I'm at, and ask how to proceed.

---

## Project layout

| Path | Logical name | Purpose |
|------|-------------|---------|
| `case_study/RiscvPmp/` | `Katamaran.RiscvPmp` | RISC-V PMP case study |
| `case_study/RiscvPmp/BlockVer/` | `…BlockVer` | Linear (block) verifier |
| `case_study/RiscvPmp/CFGVer/` | `…CFGVer` | CFG verifier (active work) |
| `theories/` | `Katamaran` | Core framework |

`_CoqProject` defines the `-Q` mappings and the exact compilation order.
CFGVer compilation order: `Spec.v` → `Verifier.v` → `Examples.v`.

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

> **⚠ gmap pivot (2026-07-13, commits `5ea9fba4`/`9b4f16be`/`0c44f2be`).**
> Instructions are now stored in a **`gmap (bv xlenbits) AST`** keyed by ABSOLUTE
> pc, NOT a `list AST` with a base+offset. `Verifier.v` has **no `base`**, no
> `instrAligned` guard, no modulo/index arithmetic — the executor does exact
> `instrs !! v` lookup. `base` survives only in `Examples.v`, converted at the
> boundary by `instrs_of_list`. This removed the `init_addr=0` limitation:
> `valid_cmovznz4_cfg_contract_at_start` (init_addr = 256) is axiom-clean.
> Sections below reflect the post-pivot API. See memory `project-cfgver-gmap-pivot`.

### `sexec_cfg_addr` / `cexec_cfg_addr`

Symbolic/concrete CFG executor. Signature:

```coq
sexec_cfg_addr (instrs : gmap (bv xlenbits) AST) (exitCond : bv xlenbits -> bool) (fuel : nat)
  : ⊢ STerm ty_xlenbits -> SHeapSpec (STerm ty_xlenbits)
```

At each step: `angelic_binary` (existential choice) between exiting and executing
the instruction at the current pc. `angelic_binary m1 m2 Φ h = m1 Φ h \/ m2 Φ h`.

Stops with `error` when:
- `fuel = 0`
- `term_get_val apc = None` (symbolic, non-concrete address)
- `instrs !! v = None` (no instruction mapped at this pc)

(No alignment/base guard: the map key IS the absolute pc.)

### `instrAligned`

Still **defined** in `Verifier.v` (`(N.to_nat (bv.bin v) mod bytes_per_instr =? 0)%nat`,
`Arguments … : simpl never`) but **no longer used** by the executor or any
soundness lemma after the gmap pivot. Vestigial; candidate for removal.

### `semTripleCFG`

```coq
Definition semTripleCFG PRE (instrs : gmap (bv xlenbits) AST) exitCond fuel POST : iProp Σ :=
  (∀ a,
     (PRE a ∗ pc ↦ᵣ a ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs instrs) -∗
     (∀ an, ⌜match an with SyncVal v => exitCond v = true | NonSyncVal _ _ => True end⌝ ∗
            pc ↦ᵣ an ∗ (∃ v, nextpc ↦ᵣ v) ∗ ptsto_instrs instrs ∗ POST a an
            -∗ WP2_loop) -∗
     WP2_loop)%I.
```

`WP2_loop` here is `BlockVer.Verifier.WP2_loop`. As before, the actual soundness
bridge used by `Examples.v` is `sound_sblock_verification_condition_myWP2`, which
goes straight to `myWP2_loop`, bypassing `semTripleCFG`. `semTripleCFG` and the
WP2-based `sound_*` in `Verifier.v` are effectively dead (kept as reference).

### `ptsto_instrs` (gmap)

```coq
Definition ptsto_instrs (instrs : gmap (bv xlenbits) AST) : iProp Σ :=
  ([∗ map] a ↦ i ∈ instrs, interp_ptsto_instr (SyncVal a) (SyncVal i))%I.
```

`ptsto_instrs_lookup instrs v Hlk` (`Hlk : instrs !! v = Some i`, via
`big_sepM_lookup_acc`) replaces the old `ptsto_instrs_nth`. `i` is implicit.

### `sblock_verification_condition` (CFGVer)

```coq
sblock_verification_condition {Σ : LCtx}
  (req : Assertion (Σ ▻ "a"∷ty_xlenbits))
  (instrs : gmap (bv xlenbits) AST)
  (exitCond : bv xlenbits -> bool)
  (fuel : nat)
  (ens : Assertion (Σ ▻ "a"∷ty_xlenbits ▻ "an"∷ty_xlenbits))
  (w : World) : 𝕊 w
```

Call pattern: `sblock_verification_condition (Σ := [ctx]) req instrs exitCond fuel ens wnil`.
`Σ := [ctx]` must be explicit — Coq cannot infer it. No `base` argument (removed).
`Examples.v`'s `CFG_VC_triple` builds `instrs` via `instrs_of_list (bv.of_N init_addr) i`.

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
`+` for angelic_binary sub-goals, `--` for refine_bind sub-goals, `*` for the gmap
lookup Some/None cases.

**gmap gotcha (cost hours):** in the execute branch the goal is
`ℛ⟦…⟧ (match instrs !! v …) (match instrs !! v …)`. A plain `destruct (instrs !! v)`
binds the case variable but does **not** reduce the `match` — `instrs !! v` inside
the `ℛ⟦⟧` relation carries hidden `Lookup`-instance implicits that a freshly-typed
`instrs !! v` doesn't match (so `destruct`/`remember`/`rewrite` all report "found no
subterm"). Result: `refine_bind` then diverges unifying `bind` against an unreduced
`match` (looks like a `Qed` hang). Fix — capture the goal's exact scrutinee:
`lazymatch goal with |- context[match ?x with Some _ => _ | None => _ end] => destruct x as [i|] end`.

---

## Soundness chain (CFGVer)

End-to-end noninterference is **complete for every example** and axiom-clean,
post-gmap-pivot. The end lemmas are `<prog>_noninterferent : noninterferent_strong
init_addr instrs exitCond reg_specs mem_specs`, each proved in one shot by
`eapply gen_contract_noninterferent; [ … 4 bullets … ]` (NoDup, HDataAddrs, length
bound, the `valid_<prog>_cfg_contract` VC). The chain:

```
valid_<prog>_cfg_contract   (vm_compute. solve_vc.)   — the symbolic VC over
        ↓  safeE (postprocess (sblock_verification_condition                 the gmap
             (extend_to_minimal_pre P) (instrs_of_list (bv.of_N init_addr) i) …))
sound_sblock_verification_condition_myWP2   (gmap; no base/instrAligned)
        ↓  → myWP2_loop ExitCondIprop
cfg_instrs_verified / cfg_instrs_safe  →  exitCond_WP2_loop
cfg_instrs_endToEnd(_with_memory)  →  gen_contract_noninterferent
        ↓  adequacy_gen_RiscVNStepsExitCond + memory (instrsAndDataMemory)
        → concrete leakage equivalence
```

The gmap pivot **resolved** the old "other programs" open problem: the executor
loop soundness (`sound_exec_cfg_addr_myWP2`) is proved generically by exact
`instrs !! v` lookup + `ptsto_instrs_lookup`, with no base/alignment/index side
conditions. `sound_sblock_verification_condition_myWP2` bridges VC soundness
straight to `myWP2_loop`.

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

> **⚠ Stale code blocks below.** The signatures shown here predate both the
> `init_addr` parameterization and the gmap pivot. Current reality (verify against
> `Examples.v`): `reg_spec := RegIdx * bool * option (Val ty_xlenbits)`; there is
> also a `mem_full_spec`; `gen_contract (init_addr : N) (reg_specs) (mem_specs)
> (instrs : list AST) (ec) (fl)`; the contract precondition is
> `asn_init_pc (bv.of_N init_addr) ∗ gen_pre reg_specs ∗ gen_mem_pre mem_specs`.
> The instruction *list* is converted to a gmap by `CFG_VC_triple` via
> `instrs_of_list (bv.of_N init_addr) i`. The once-and-for-all end lemma is
> `gen_contract_noninterferent` (no `Hbase`/`instrAligned` param — removed).

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

> **⚠ Post-pivot deltas** (the block below predates the gmap pivot + `Hbase`
> removal): the `cfg_instrs_*` chain now carries `ptsto_instrs (instrs_of_list
> (bv.of_N init_addr) instrs')` (gmap), NOT `ptsto_instrs (SyncVal base) b`; the
> `Hbase : instrAligned … = true` parameter is **gone** from `cfg_instrs_verified`
> / `_safe` / `_with_mem` / `cfg_instrs_endToEnd(_with_memory)` /
> `gen_contract_noninterferent`. Memory is materialized by `instrsMemory` /
> `instrsAndDataMemory`, which now produce the gmap `ptsto_instrs`.

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

> **⚠ gmap pivot note.** `instrsAndDataMemory` and `intro_ptsto_instrs` now yield the
> gmap `Katamaran.RiscvPmp.CFGVer.Verifier.ptsto_instrs (instrs_of_list (bv.of_N start)
> instrs)` (via `big_sepM_insert`, side condition `instrs_of_list_fresh`), NOT the old
> list `ptsto_instrs (SyncVal base) instrs`. The `interp_mem_with_*` data-memory
> machinery is unchanged.

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

### `instrsAndDataMemory`

Extracts `ptsto_instrs ∗ interp_mem_with_memory` from the raw `mem_res2_without_leak`.
Data words must occupy the `4*|data_specs|` bytes immediately following the instruction
region.

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

`instrsAndDataMemory` is proved.

---

## Binary WP semantics (`semWP2_unfold`)

`IVal τ = Val τ + string` — `inl v` is a success value, `inr m` is a failure string.

`stm_to_val` maps `stm_val _ v ↦ Some(inl v)`, `stm_fail _ m ↦ Some(inr m)`, and all
non-terminal statements to `None`.

`semWP2_fix` / `semWP2_unfold` distinguish four terminal cases:

| `stm_to_val s1` | `stm_to_val s2` | Result |
|-----------------|-----------------|--------|
| `Some(inl v1)` | `Some(inl v2)` | `POST (inl v1) δ1 (inl v2) δ2` |
| `Some(inr m1)` | `Some(inr m2)` | `POST (inr m1) δ1 (inr m2) δ2` |
| mixed (inl×inr or inr×inl) | — | `\|={⊤}=> False` |
| `None` (either side) | — | stepping cases |

Consequence for proofs: when **both** sides are concrete constructors (`stm_val`/`stm_fail`),
`cbn` after `rewrite semWP2_unfold` immediately reduces to the correct branch — no
`env.drop_cat` terms appear. When one side is an abstract stepping statement, partial
match arms with `env.drop` terms are still visible.

`Result2` in `BinaryAdequacy.v` has the same structure: `Some(inl)×Some(inl)` and
`Some(inr)×Some(inr)` call POST; everything else reduces to `False`.

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
| `rewrite !env.drop_cat` fails after `rewrite !semWP2_unfold; cbn` for val×fail or fail×val bullets | Both `stm_to_val`s are concrete, so `cbn` collapses the match immediately to `\|={⊤}=> False` — no `env.drop` terms survive. Replace with `do 3 iModIntro. iMod "Hclose". iMod "WPk". auto.` |
| `iMod "H"` fails with "cannot eliminate modality match i with \| inl … \| inr … end" in adequacy proof | After `case_match` introduces `i : IVal τ` (abstract), `H` has type `match i with …`. Iris `iMod` requires syntactic `\|={E}=> P`. Add `destruct i as [v2\|m2].` before `iMod`. |
| Second `{ inversion H. }` bullet gives `[Focus] No such goal (1)` in `semWP2_call_frame`-style proof | For val×step or step×val cases, the `stm_fail` sub-case now produces `WPs : \|={⊤}=> False`, which `try solve [… iMod "WPs"; auto]` closes immediately. Remove the trailing `{ inversion H. }` for those cases only (keep it for fail×step and step×fail where `inr×inr` gives POST). |
| `lia` fails "Cannot find witness" on a trivial linear N goal in `Examples.v` | `From stdpp Require Import gmap` activates a Zify rewrite turning `bv.bin (bv.of_N x)` into `x mod 2^word`; the huge modulus breaks lia's certificate search. Make the atom opaque first: `set (B := bv.bin (bv.of_N …)) in *; clearbody B. lia.` (Bare `bv.bin a` is fine — only the `bin∘of_N` composition triggers it.) |
| `lia` fails on a goal bounded by `bv.exp2 xlenbits` (= 2^32) | lia chokes evaluating the literal `4294967296`. Bound to a small literal then transit (`assert (… < 1024) by lia; eapply N.lt_trans; [exact Hb\|]; reflexivity`), or make exp2 opaque (`set (E := bv.exp2 xlenbits) in *; clearbody E; lia`). |
| SSReflect `rewrite … in H by tac` fails to parse in `Examples.v` | BlockVer imports SSReflect, whose `rewrite` rejects the Ltac `by` clause. Provide conditional-lemma side conditions as explicit hypotheses (`assert (Hs : …) by (…); rewrite (lem Hs) in H`) instead. |
| `destruct (instrs !! v)` binds the case var but leaves `match instrs !! v` unreduced (then `refine_bind`/`iApply` hangs) | The lookup inside `ℛ⟦⟧`/relational goals carries hidden `Lookup`-instance implicits. Capture the goal's exact scrutinee: `lazymatch goal with \|- context[match ?x with Some _ => _ \| None => _ end] => destruct x as [i\|] end`. |
| `rocq_start(theorem=X)` "succeeds" but a prior proof was actually broken | Theorem/position starts load the prefix vos-style (proof bodies SKIPPED). Only `rocq_check` of a body or a `mode=full` compile actually runs proofs. Don't infer a lemma passed just because a later `rocq_start` reached it. |
| `set`/`rewrite` silently fails to match a bv-indexed lemma after `cbn` | A blanket `cbn` unfolds `xlenbits` (`:= xlenbytes * byte`) into unary Peano `S (S (… O))`; lemmas proved with the folded index then differ syntactically (though convertibly — `apply`/`exact` still work). Use `cbn -[xlenbits]` when the goal will be matched against an external bv-indexed lemma. |
| `try (eapply L; eauto)` in a tactic leaves stray side-condition goals | `eauto` never fails (it succeeds doing nothing), so the unit is NOT failure-atomic: on a conclusion-matching goal with underivable side conditions it commits to `eapply` and leaves the side goals behind. Wrap as `try (solve [eapply L; eauto])` for discharge-or-revert. |
| `rsolve` eats multi-GB RAM / rocq-mcp pet dies with `memory_exhausted` | rsolve reached a goal pairing heads with no matching `RefineCompat` instance (e.g. `cexec_cfg_addr` vs `sexec_cfg_addr_tbl`, or two monadic programs whose bind structures are misaligned) and typeclass search diverged. Pair the binds manually (`iApply (HeapSpec.refine_bind (RA := …))`, `rsolve` only on aligned atomic subgoals), dispatch the table executor with `rexec_cfg_addr_tbl`. |
| `iApply my_lemma` fails with "variable not found" for a lemma proven earlier in the same rocq-mcp session | Nested Proofs are allowed in this codebase: a missing `Qed.` does NOT error — the next `Lemma` silently opens a nested proof and the previous name never enters the environment. Verify the `feedback` field shows "X is defined" after every `Qed.`. |
| Plain `refine_bind` resolves to the PureSpec variant, `iApply` fails on a CHeapSpec/SHeapSpec goal | `Import PureSpec.` (Verifier.v Relational section, ~line 604) shadows the HeapSpec names for everything below it. Qualify: `HeapSpec.refine_bind`. |

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

## Example status (post-gmap-pivot)

All CFGVer examples compile with **zero `Admitted`** in `Examples.v`; each has a
`valid_<prog>_cfg_contract` VC (`vm_compute. solve_vc.`) and a `<prog>_noninterferent`
end-to-end lemma (`eapply gen_contract_noninterferent; […]`). Examples: `swap`,
`jumpIfZero`, `jmp_fwd`, `countdown`, `countdown_mem`, `set_X2_to_42`, `cmovznz4`,
and **`cmovznz4_at_start`** (init_addr = 256, genuinely nonzero base).

`valid_cmovznz4_cfg_contract_at_start` is **"Closed under the global context"**
(axiom-clean) — the headline result: cmovznz4 verified at a nonzero base through
the finite-map executor.

`valid_jmp_fwd` (BlockVer, `Section WithAsnNotations`) stays **Admitted** — BlockVer
cannot handle JAL; that's what CFGVer is for.

---

## Updating this file

This file should be updated whenever:
- A new lemma / definition pattern is discovered
- A common pitfall is encountered and resolved
- The soundness chain is extended
- New imports or module structure changes occur

Previous Claude sessions: commits tagged `WIP (LLM):` are primarily LLM-generated.
