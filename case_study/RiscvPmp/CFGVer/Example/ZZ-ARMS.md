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

