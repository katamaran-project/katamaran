# `ctx.fresh` — measured, and it is not a driver

> **STAGE SPLIT, 2026-09-08 — 0% tactic.**  The per-call arms
> (`ZZFreshBench*`) are standalone microbenchmarks that never build a VC, and
> the real-traffic arm (`ZZDSI206`) is a bare `Eval vm_compute`.  No `solve_vc`
> in any of them, so the 0.32-0.48% verdict is about the executor and is not
> diluted by a tactic.  See `vm-vs-tactic-split.md`.

Status: **Diagnostic record, 2026-09-02.** Closes the "FRESH-NAME GENERATION"
entry in the `cfgver-scaling-diagnostics` driver catalog, which stood as
*"not yet isolated, cheapest possible fix … named as the recommended next
experiment; do not quote a magnitude, none was measured."* A magnitude now
exists and the recommendation is **withdrawn**.

## One-sentence finding

`ctx.fresh` costs **0.32 %–0.48 % of total allocation** at K=206 on the muladd
rig — so the ceiling on *any* fix to it (fused scan, counter naming, hash set)
is under half a percent — and its share **falls** as K grows (0.59 % → 0.48 %
over K=162→206), because the traffic it generates grows at 1.853× while total
cost grows at 2.283×.

## 1. Why it looked promising

`Context.v:707` scans the whole context up to three times per mint:

```coq
Definition fresh [T : Set] (xs : NCtx string T) (x : option string) : string :=
  let xs := names xs in                                   (* (1) allocate |Σ| cons cells *)
  let x := match x with Some x => x | None => "x" end in
  if List.find (String.eqb x) xs                          (* (2) |Σ| string compares *)
  then let base := fst (split_at_dot x) in
       let n    := N.succ (max_with_base base xs) in      (* (3) |Σ| × split_at_dot + parse *)
       String.append base (String "." (unparse_number n))
  else x.
```

and it is called once per symbolic variable, from `SPureSpec.angelic` /
`SPureSpec.demonic` (`Symbolic/Monads.v:300,307`). The per-step mints (`"a"`,
`"np"`, `"na"` — `Verifier.v:188,501,507`) **always** collide, so branch (3)
always runs: traced by hand, the first `demonic (Some "a")` returns `"a"`, the
second finds `"a"` present and returns `"a.1"`, the third `"a.2"`, and so on.
`split_at_dot` rebuilds each name character by character through a CPS
accumulator, allocating per character — so (3), not (1), is the bulk of it.
That is `O(mints × |Σ| × namelen)`, chunk-free, and it looked like a textbook
quadratic with a free fix.

## 2. The experiment

Two independent measurements, multiplied. No `theories/` rebuild was needed for
either, which is why this cost four small runs rather than a double sweep.

| axis | how it was measured | file |
|---|---|---|
| **cost per `fresh` call**, as a function of context size | microbenchmark: R calls on a fixed context of *n* bindings named `"a"`, `"a.1"` … `"a.n"`, so the requested base always collides and branch (3) always runs | `Example/ZZFreshBench{33,96,135}.v`, baseline `ZZFreshBenchB.v` |
| **`fresh` traffic in the real run**: number of calls, and the context size at each | `zz_stats_raw` on the muladd dense-havoc prefix — `lv_binders` counts `angelicv`/`demonicv` nodes (= mints), `lv_sigint` sums `|Σ|` over exactly those nodes (= total entries scanned, one scan) | `Example/ZZDSI{162,206}.v` |

Protocol tag: **ALLOC** (`OCAMLRUNPARAM='v=0x400'`, one `Eval vm_compute` per
process, net of a no-`Eval` baseline). No `Qed`, no `solve_vc` — **not**
comparable to any `Qed`-protocol figure in this repo (that mismatch is worth
1.81×).

## 3. Results

### 3.1 Per-call cost (2000 calls, net of baseline 47,417,983)

| ctx entries | net words | words/call | words/entry |
|---|---|---|---|
| 34 | 3,030,545 | 1,515 | 44.6 |
| 97 | 9,728,922 | 4,864 | 50.1 |
| 136 | 15,234,753 | 7,617 | 56.0 |

Words-per-entry rises with *n* because the generated names get longer
(`a.9` → `a.135`), so `split_at_dot`'s per-character cost rises with the
context — mildly super-linear, as expected from branch (3).

**Linearity check in the call count, and a discrepancy.** At n=136, doubling
R from 2000 to 4000 gave 33,740,732 net — **2.215×**, not 2.000×. I could not
account for the extra 11 % (it is not a fixed offset — that would make the
ratio *under* 2). Rather than explain it away, both readings are carried
below: the **direct** slope (7,617 w/call, 56 w/entry) and the **marginal**
R=2000→4000 slope (9,253 w/call, 68 w/entry), which is the conservative one.
The conclusion does not depend on which is used.

### 3.2 Real traffic, and the resulting share

`lv_maxsig` reproduces §7.1 of `theories/diagnostics/env-lookup-cost-drivers.md`
(peak `|Σ|` = 96 at K=162, 135 at K=206), confirming this is the same rig.
Denominators are that file's §7.1 NEW-arm net totals.

| K | mints | `lv_sigint` | peak `\|Σ\|` | avg `\|Σ\|` at mint | `fresh` (lo) | `fresh` (hi) | total | **share** |
|---|---|---|---|---|---|---|---|---|
| 162 | 3,082 | 137,914 | 96 | 44.7 | 6.34 M | 9.38 M | 1.5927 G | **0.40 – 0.59 %** |
| 206 | 4,152 | 255,568 | 135 | 61.6 | 11.76 M | 17.38 M | 3.6358 G | **0.32 – 0.48 %** |

No fit and no held-out point: two points is not a law, and none is claimed.
The claim is a **bound**, and it is insensitive to every assumption in it —
the traffic figure would have to be ~20× low to reach even 10 %.

### 3.3 The one caveat

`lv_binders` counts the **raw** tree (`zz_vc_raw`, pre-`postprocess`), so mints
on paths pruned *during* construction are not counted. This is therefore a
lower bound on the call count. It is a small undercount — the tree is raw — and
it cannot plausibly close a 200× gap.

## 4. Reading the axes apart

**The share falls with K.** Over K=162→206:

| quantity | growth |
|---|---|
| mints (`lv_binders`) | 1.347× |
| entries scanned (`lv_sigint` = mints × avg depth) | 1.853× |
| **total cost** | **2.283×** |

`fresh` generates work proportional to `lv_sigint`, which grows *slower* than
total cost. So it is not merely small, it is **shrinking as a fraction** —
exactly the wrong shape for something to invest in.

**The same table is a second, independent reading of the `|Σ|` quadratic.**
`lv_sigint` is precisely the cost a model of "each mint does `O(|Σ|)` work"
predicts, and it grows 1.853× where the real cost grows 2.283×. A model of
`O(|Σ|²)` per mint predicts ≈2.56× (`mints × avg|Σ|²`, ignoring variance in the
depth distribution — so this is indicative, not a fit). The observed 2.283×
sits between, nearer the quadratic. Per-mint work is therefore **superlinear in
`|Σ|`**, which is consistent with the catalog's un-isolated candidate:
`sub_comp` maps `subst` over an `Env` of `|Σ|` terms, each doing an `O(|Σ|)`
lookup, so composing two substitutions is `O(|Σ|²)` and the executor composes
one per world extension. **Not established here** — two points and a
variance-free approximation cannot establish an exponent — but it is the first
evidence pointing at `sub_comp` from the measurement side rather than from
reading the code.

**Incidental:** `lv_vareqs` (4,031) against `lv_binders` (4,152) — 97 % of every
variable minted is retired again inside the same tree. The churn is real; it is
just not `fresh` that makes it expensive.

## 5. What this means

- **`ctx.fresh` is closed.** Do not fund a fix. The catalog bullet naming it as
  "the recommended next experiment" is withdrawn.
- **A fused scan would not have helped even if it were free.** Worth recording
  separately, because it was the obvious cheap move: fusing `names` away
  removes only step (1)'s cons cells, while the per-element cost is dominated
  by `split_at_dot` in step (3). The cheap fix attacks the small half of an
  already-negligible cost.
- **The naming scheme cannot be replaced cheaply anyway.** `fresh` must be a
  pure function of the context, because its result lands in a type
  (`wsnoc w (y∷σ)`). A mutable counter cannot be threaded through it; the
  asymptotic fix would need de Bruijn-level naming or a memo carried in
  `World`, both invasive, and both now known to be worth <0.5 %.
- **Next lead is `sub_comp`**, on §4's evidence, not `fresh`.

## 6. Files / reproduction

Probes are gitignored throwaways under `Example/`, per the `ZZ*.v` convention.

```bash
# per-call cost -- needs only theories/, no CFGVer build
for f in ZZFreshBenchB ZZFreshBench33 ZZFreshBench96 ZZFreshBench135; do
  OCAMLRUNPARAM='v=0x400' coqc -q -w none -R theories Katamaran \
    case_study/RiscvPmp/CFGVer/Example/$f.v 2>&1 | grep -E 'allocated_words|Error'
done

# real traffic
OCAMLRUNPARAM='v=0x400' coqc -q -w none -Q case_study/RiscvPmp Katamaran.RiscvPmp \
  -R theories Katamaran case_study/RiscvPmp/CFGVer/Example/ZZDSI206.v 2>&1 \
  | grep -A9 lv_binders
```

`ZZFreshBench<n>.v` is `ZZFreshBenchT.v` with `Definition NN` sed'd;
`ZZFreshBenchB.v` is it with the final `Eval` line deleted. `ZZDSI<K>.v`
derives from `Example/ZZMuladdFullN2.v` — see `muladd-full-cost-drivers.md` §5.

---

**Sequel:** the same session went on to hunt `Base(K)` itself with the same
two-measurement method. That is a separate causal question and lives in
`base-k-hunt.md` — which refutes the `AMessage` hypothesis outright (0.00 % of
peak heap) and records the `sub_wk1` Θ(|Σ|²) finding.
