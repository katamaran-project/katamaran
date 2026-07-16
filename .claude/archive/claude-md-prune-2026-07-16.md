# Archive: CLAUDE.md prune of 2026-07-16

Verbatim copy of everything removed from CLAUDE.md in the skills refactor, with
destinations. Nothing here is lost: every row either lives in a skill now or was
retired as stale. This file is never auto-loaded; it exists for human reference.

Plugin-coverage check (2026-07-16): the LLM4Rocq rocq plugin was verified NOT to
cover bullet discipline, eauto non-atomicity, SSReflect rewrite quirks, or
Set Printing debugging — those went to the project skill `rocq-pitfalls` instead
of being deleted.

## Destination map

| Destination | Rows |
|---|---|
| folded into CLAUDE.md "rocq-mcp workflow" | physical-path, rocq_start-vos, nested-Qed |
| `rocq-pitfalls` skill (new) | wrong-bullet, try-eapply-eauto, SSReflect-by, SSReflect-comma, + the "Essential Rocq debugging commands" section |
| `bv-pitfalls` skill (new) | bv.finite.elem_of_enum, lia-exp2, cbn-xlenbits-Peano |
| `gmap-pitfalls` skill | (moved earlier: destruct-lookup-match, gmap-import-zify-lia) |
| `iris-proofmode` skill | iFrame-No-such-goal, Is_true, iApply-needs-unfold, fancy-update-True, ImplPre-Σ', second-iFrame, iMod-modality-match, Hmemdata-empty-context |
| `cfgver-executor` | Σ-implicit |
| `cfgver-rsolve` | rsolve-hangs, rsolve-memory_exhausted, PureSpec-shadowing |
| `cfgver-soundness` | exitCond_WP2_loop-form |
| `cfgver-wp2` | env.drop_cat, iMod-match, inversion-No-such-goal, Is_true |
| `cfgver-endtoend` | @cfg_instrs_endToEnd, vm_compute-scoping |
| `cfgver-endtoend-internals` | ImplPre-Σ', second-iFrame, safe_with_mem-args, Hmemdata |
| `cfgver/references/registers.md` | Forall_nil, declare_pub_head_true-implicit, something_registers-direction |
| `cfgver` hub | "Importing CFGVer.Verifier" section, "Example status" section |
| retired as stale (dead API) | Cannot-infer-exitCond (references the dead `sound_cexec_triple_addr` direct-apply path) |

## The full pitfalls table as it stood

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
| `lia` fails on a goal bounded by `bv.exp2 xlenbits` (= 2^32) | lia chokes evaluating the literal `4294967296`. Bound to a small literal then transit (`assert (… < 1024) by lia; eapply N.lt_trans; [exact Hb\|]; reflexivity`), or make exp2 opaque (`set (E := bv.exp2 xlenbits) in *; clearbody E; lia`). |
| SSReflect `rewrite … in H by tac` fails to parse in `Examples.v` | BlockVer imports SSReflect, whose `rewrite` rejects the Ltac `by` clause. Provide conditional-lemma side conditions as explicit hypotheses (`assert (Hs : …) by (…); rewrite (lem Hs) in H`) instead. |
| SSReflect `rewrite h1, h2.` (comma) is a syntax error | Under SSReflect, chain rewrites space-separated: `rewrite h1 h2.` |
| `rocq_start(theorem=X)` "succeeds" but a prior proof was actually broken | Theorem/position starts load the prefix vos-style (proof bodies SKIPPED). Only `rocq_check` of a body or a `mode=full` compile actually runs proofs. Don't infer a lemma passed just because a later `rocq_start` reached it. |
| `set`/`rewrite` silently fails to match a bv-indexed lemma after `cbn` | A blanket `cbn` unfolds `xlenbits` (`:= xlenbytes * byte`) into unary Peano `S (S (… O))`; lemmas proved with the folded index then differ syntactically (though convertibly — `apply`/`exact` still work). Use `cbn -[xlenbits]` when the goal will be matched against an external bv-indexed lemma. |
| `try (eapply L; eauto)` in a tactic leaves stray side-condition goals | `eauto` never fails (it succeeds doing nothing), so the unit is NOT failure-atomic: on a conclusion-matching goal with underivable side conditions it commits to `eapply` and leaves the side goals behind. Wrap as `try (solve [eapply L; eauto])` for discharge-or-revert. |
| `rsolve` eats multi-GB RAM / rocq-mcp pet dies with `memory_exhausted` | rsolve reached a goal pairing heads with no matching `RefineCompat` instance (e.g. `cexec_cfg_addr` vs `sexec_cfg_addr_tbl`, or two monadic programs whose bind structures are misaligned) and typeclass search diverged. Pair the binds manually (`iApply (HeapSpec.refine_bind (RA := …))`, `rsolve` only on aligned atomic subgoals), dispatch the table executor with `rexec_cfg_addr_tbl`. |
| `iApply my_lemma` fails with "variable not found" for a lemma proven earlier in the same rocq-mcp session | Nested Proofs are allowed in this codebase: a missing `Qed.` does NOT error — the next `Lemma` silently opens a nested proof and the previous name never enters the environment. Verify the `feedback` field shows "X is defined" after every `Qed.`. |
| Plain `refine_bind` resolves to the PureSpec variant, `iApply` fails on a CHeapSpec/SHeapSpec goal | `Import PureSpec.` (Verifier.v Relational section, ~line 604) shadows the HeapSpec names for everything below it. Qualify: `HeapSpec.refine_bind`. |

## "Essential Rocq debugging commands" section (→ rocq-pitfalls)

```coq
Unset Printing Notations.    (* see raw terms instead of notation *)
Set Printing Implicit.       (* show implicit arguments *)
Set Printing All.            (* show everything; very verbose *)
Set Typeclasses Debug.       (* trace typeclass search — invaluable for rsolve failures *)
```

Reset with the `Un/Set` inverse. Use `Print refine_compat_block_verification_condition.`
to inspect specific instances.

## "Importing CFGVer.Verifier into Examples.v" section (→ cfgver hub)

```coq
(* At top level, after the main Require Import block: *)
From Katamaran Require
     RiscvPmp.CFGVer.Verifier.
```

Then use qualified: `Katamaran.RiscvPmp.CFGVer.Verifier.sblock_verification_condition`.
Do NOT `Require Import` — it causes notation/name conflicts with BlockVer.

## "Example status (post-gmap-pivot)" section (→ cfgver hub, updated there)

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
