# ZZ diagnostic arms — exact interventions (THROWAWAY, delete with the ZZ*.v probes)

Root cause of the CFGVer loop scaling wall (2026-07-29): the **live
logic-variable context**, not term size / |wco| / nodes / heap / postprocess.
Full record in the `project-key-schedule-loop-scaling` memory note and in the
`cfgver-executor` skill's "Backward-branch loops" caveat.

Harness: `ZZCommon.v` (definitions + 12-counter node census; `Require Export`
so downstream files get the notations) plus `ZZRun1/2/4.v` (ONE heavy `Eval` per
`coqc` process -- several in one process contaminate each other) and
`ZZNames.v` (demonicv names vs assume_vareq-eliminated names).
`ZZProbeStages/Heap/Nodes.v` are the earlier, superseded multi-Eval versions.

Results at N=4 (flat reproducer, `addi a0,a1,1` x10 so every term is O(1)):

| arm | wco/trip | net live wctx/trip | N=1 | N=2 | N=4 | vs base |
|---|---|---|---|---|---|---|
| REMOVAL  | 1 (/15)  | 29         | 1.25 | 6.55 | 16.52 | 0.82x |
| BASELINE | 15       | 29         | 1.46 | 7.10 | 20.19 | 1.00x |
| WCTX     | 15       | 57 (x1.97) | 3.53 | 10.53 | 44.29 | **2.19x** |
| PADDED   | 43 (x2.9)| 57 (x1.97) | 4.65 | 12.46 | 58.16 | 2.88x |

WCTX moved exactly ONE census counter (`demonicv` 629->741); PADDED moved two,
so only WCTX is a clean single-variable arm. Reproduce by applying one diff
below to `CFGVer/Spec.v`, rebuilding `make -f Makefile.coq -j2
case_study/RiscvPmp/CFGVer/Example/Prelude.vo` (~42 s), then `coqc` each ZZRun.

## unquantify (fifth arm, 2026-07-29) — POST-HOC PRUNE, NOT A FIX

Branch `unquantify-gate` (off `bearssl-breaking-bad`), commits d301d482..bcecaaea:
`main`'s `unquantify` pass (`theories/Symbolic/GenOccursCheck.v` +
`Propositions.v`'s `Section Unquantify`) ported over, definitions only, all
soundness `Admitted` — a measurement, not a verification. Harness:
`ZZUnqCommon.v` + `ZZUnqRun{1,2,4}{base,pp}.v` + `ZZUnqRun1raw.v`.

Note this arm was measured on the REMOVAL tree (the `secLeakvar "encoded_instr"`
drop is permanent as of ceb86848), so compare against REMOVAL, not BASELINE.

Dead-binder census, `nc_demonicv` (every OTHER counter identical between the two
columns at every N — the required control: nothing but binders moved):

| N | postprocess only | postprocess + unquantify |
|---|---|---|
| 1 | 32  | **1** |
| 2 | 56  | **1** |
| 4 | 114 | **1** |

The residual is a CONSTANT 1 regardless of N — the contract's own top-level
base-address existential `"p"`, genuinely used in every fetch-bound formula.
So ~all of `|wctx|`'s demonicv-driven growth is occurrence-dead by the end.
Unquantify applied to the RAW pre-postprocess tree is far weaker (residual 146
at N=1): `postprocess`-first is the composition that matters, because
`solve_uvars`' substitutions are what expose the redundancy to the occurs check.

Timing, same nine runs, one `Eval` per `coqc` process:

| N | raw VC gen | + postprocess | + postprocess + unquantify | unq marginal |
|---|---|---|---|---|
| 1 | 1.031 s  | 1.066 s  | 1.070 s  | +0.4% |
| 2 | 6.654 s  | 6.715 s  | 6.794 s  | +1.2% |
| 4 | 16.551 s | 16.761 s | 16.935 s | +1.0% |

**Unquantify costs time, it does not save it, and the scaling exponent is
untouched**: N=1->N=4 growth is 16.0x raw, 15.7x postprocess, 15.8x
postprocess+unquantify. Peak RSS at N=4 is 3333/3336/3336 MB. The port itself
perturbed nothing — raw generation matches the pre-port REMOVAL row (1.25/6.55/
16.52) within the run-to-run spread this harness's own header documents.

Reading: the 113 binders dropped at N=4 were PAID FOR during `vm_compute` —
every intermediate world carried them and every `persist`/`subst`/solver call
ranged over them. Deleting them from the finished tree refunds none of that.
This arm is therefore a FEASIBILITY result only: it says a forward world-GC
would find ~29 dead variables per trip and would be correct to drop them. See
`../PLAN-unquantify-forward.md` for the plan that acts on it.

## removal

(Recovered from the working tree, where this intervention was present at the
time of writing -- the job-tmp copy was never saved. Just delete the
`secLeakvar "encoded_instr"` conjunct from the fetch postcondition.)

```diff
--- a/case_study/RiscvPmp/CFGVer/Spec.v
+++ b/case_study/RiscvPmp/CFGVer/Spec.v
@@ -310,8 +310,7 @@ Module RiscvPmpCFGVerifSpec <: Specification RiscvPmpBase RiscvPmpSignature Risc
          asn.chunk (chunk_ptsreg pc (term_var "a")) ∗ term_var "a" ↦ᵢ term_var "i" ∗
          asn.exist "encoded_instr" _
          (term_var "result_fetch" = term_union fetch_result KF_Base (term_var "encoded_instr") ∗
-                                      asn.chunk (chunk_user encodes_instr [term_var "encoded_instr"; term_var "i"])
-         ∗ secLeakvar "encoded_instr") ∗
+                                      asn.chunk (chunk_user encodes_instr [term_var "encoded_instr"; term_var "i"])) ∗
            asn_cur_privilege (term_val ty_privilege Machine) (* ∗ *)
            (* asn_pmp_entries (term_var "entries") *);
     |}.
```

## padded

```diff
@@ -310,7 +310,14 @@
          asn.chunk (chunk_ptsreg pc (term_var "a")) ∗ term_var "a" ↦ᵢ term_var "i" ∗
          asn.exist "encoded_instr" _
          (term_var "result_fetch" = term_union fetch_result KF_Base (term_var "encoded_instr") ∗
-                                      asn.chunk (chunk_user encodes_instr [term_var "encoded_instr"; term_var "i"])) ∗
+                                      asn.chunk (chunk_user encodes_instr [term_var "encoded_instr"; term_var "i"])
+         ∗ secLeakvar "encoded_instr") ∗
+         (* ZZ DIAGNOSTIC PADDING -- two fresh existentials each carrying an
+            undischargeable secLeak, produced at every fetch: wco growth per
+            trip goes 15 -> 43.  Additive, so no asserts are added and
+            execution cannot truncate. *)
+         asn.exist "zzpad1" ty_xlenbits (secLeakvar "zzpad1") ∗
+         asn.exist "zzpad2" ty_xlenbits (secLeakvar "zzpad2") ∗
            asn_cur_privilege (term_val ty_privilege Machine) (* ∗ *)
            (* asn_pmp_entries (term_var "entries") *);
     |}.
@@ -762,7 +769,7 @@
   (*            sep_contract_fetch_instr (FunDef fetch))). *)
 
   Lemma valid_execute_fetch : ValidContract fetch.
-  Proof. now vm_compute. Qed.
+  Proof. Admitted.
 
   (* Lemma valid_execute_fetch_instr : SMut.ValidContract sep_contract_fetch_instr (FunDef fetch). *)
   (* Proof. compute. Admitted. *)
```

## wctx

```diff
@@ -310,7 +310,17 @@
          asn.chunk (chunk_ptsreg pc (term_var "a")) ∗ term_var "a" ↦ᵢ term_var "i" ∗
          asn.exist "encoded_instr" _
          (term_var "result_fetch" = term_union fetch_result KF_Base (term_var "encoded_instr") ∗
-                                      asn.chunk (chunk_user encodes_instr [term_var "encoded_instr"; term_var "i"])) ∗
+                                      asn.chunk (chunk_user encodes_instr [term_var "encoded_instr"; term_var "i"])
+         ∗ secLeakvar "encoded_instr") ∗
+         (* ZZ DIAGNOSTIC: wctx-ONLY arm.  Two fresh UNCONSTRAINED demonic
+            variables with NO formula attached, so nothing ever unifies them
+            away: net live wctx growth goes 29 -> 57 per trip (1.97x), while
+            wco is left completely untouched (assumek must stay 58 at N=4 --
+            that is the control).  Mirror of the PADDED arm, which moved BOTH.
+            If this alone reproduces PADDED's ~2.9x, wctx is the driver and
+            wco is exonerated. *)
+         asn.exist "zzpad1" ty_xlenbits ⊤ ∗
+         asn.exist "zzpad2" ty_xlenbits ⊤ ∗
            asn_cur_privilege (term_val ty_privilege Machine) (* ∗ *)
            (* asn_pmp_entries (term_var "entries") *);
     |}.
@@ -761,8 +771,10 @@
   (* Eval vm_compute in (postprocess (RiscvPmpCFGVerifExecutor.SHeapSpecM.vcgen RiscvPmpCFGVerifExecutor.default_config 1 *)
   (*            sep_contract_fetch_instr (FunDef fetch))). *)
 
+  (* ZZ: Admitted to avoid a wasted rebuild if the added existential perturbs
+     the reflective check; irrelevant to the measurement. *)
   Lemma valid_execute_fetch : ValidContract fetch.
-  Proof. now vm_compute. Qed.
+  Proof. Admitted.
 
   (* Lemma valid_execute_fetch_instr : SMut.ValidContract sep_contract_fetch_instr (FunDef fetch). *)
   (* Proof. compute. Admitted. *)
```

