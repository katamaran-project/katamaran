---
name: cfgver-soundness
description: >
  Katamaran CFGVer soundness chain — the theorem-level bridge from a verified VC to
  concrete leakage-equivalence. Use when tracing, explaining, or extending the chain
  valid_<prog>_cfg_contract → (refinement to the concrete executor) →
  sound_scfg_verification_condition_myWP2 → myWP2_loop → cfg_instrs_verified/safe →
  gen_contract_noninterferent_param → adequacy_gen_RiscVNStepsExitCond → leakage_trace
  equality, or the WP2_loop vs myWP2_loop design distinction. NOT for the step-level
  mechanics of semWP2 proofs (semWP2_unfold, stm_to_val, env.drop_cat — use
  cfgver-wp2) and NOT for wiring one specific program's end lemma (use
  cfgver-endtoend).
---

# CFGVer soundness chain

The theorem layer connecting a verified VC to concrete leakage equivalence. It uses
the symbolic executor (→ **cfgver-executor**) and the refinement to the concrete
mirror (→ **cfgver-refinement**); per-program wiring is in **cfgver-endtoend**;
semWP2 proof mechanics behind the adequacy layer are in **cfgver-wp2**.

## The chain

Every example's end lemma is
`<prog>_noninterferent : noninterferent_strong init_addr instrs exitCond reg_specs mem_specs`,
proved in one shot by `eapply gen_contract_noninterferent_param` (or the matching
`_rel` / `_rel_classed` / `_rel_bytes` variant, in practice its `_simple`
specialisation) plus its side premises
(→ **cfgver-gen-contract** for the premise list). Underneath:

```
valid_<prog>_cfg_contract   (vm_compute. solve_vc.)   — the symbolic VC over the
        ↓  safeE (postprocess (scfg_verification_condition        term table
             (extend_to_minimal_pre P) tbl exits …))     (tbl/exits, not the gmap)
sound_scfg_verification_condition_myWP2  — bridges via itable_faith/etable_faith
        ↓  → myWP2_loop ExitCondIprop
cfg_instrs_verified / cfg_instrs_safe  →  exitCond_WP2_loop
cfg_instrs_endToEnd(_with_memory)  →  gen_contract_noninterferent_{param,rel,…}
        ↓  adequacy_gen_RiscVNStepsExitCond + memory (instrsAndDataMemory)
        → concrete leakage equivalence
```

Why it works generically for any program: executor-loop soundness
(`sound_exec_cfg_addr_myWP2`) needs only the exact `instrs !! v` lookup plus
`ptsto_instrs_lookup` — there are no base/alignment/index side conditions to
discharge per program. `sound_scfg_verification_condition_myWP2` then takes
VC soundness straight to `myWP2_loop`, given the `itable_faith`/`etable_faith`
facts tying the term table to that gmap at the relevant valuation.

**Extending the chain:** copy the closest existing example's `<prog>_noninterferent`
in `Example/<Prog>Result.v` as the analogue rather than deriving from scratch
(`Results.v` itself is only a re-export shell over those files).

## WP2_loop vs myWP2_loop (design distinction)

`WP2_loop` iterates the full machine loop; `myWP2_loop ExitC` carries an explicit
exit-condition proposition, which is what adequacy needs in order to know *when* the
execution stops. That is why the live bridge targets `myWP2_loop` directly, via the
table-based `sound_scfg_verification_condition_myWP2` chain in `Adequacy.v`.
`exitCond_WP2_loop` must use the `⌜exitCond v ∨ exitCond v'⌝` (Is_true
coercion) form to match `adequacy_gen_RiscVNStepsExitCond`'s statement.

---

**Stuck inside a semWP2/adequacy proof** (unreduced `match`, `env.drop_cat`, `iMod`
failing on a modality-match)? That's the **cfgver-wp2** skill.
