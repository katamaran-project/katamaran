# A multiplication that leaks its operands

**Finding: extending the leakage model with a fourth event — `LeakMul`,
carrying BOTH multiplication operands — costs the framework nothing and
changes the accepted-program set exactly where it should. No file in
`theories/` changed, no proof in the soundness chain changed, all 18
pre-existing end theorems still discharge, and a multiplication on a secret
operand goes from verifying to failing on precisely one obligation:
`secLeak` of that operand.**

Not a cost/scaling record — this directory's other files price mechanisms.
This one records a *model* change and its consequences, and lives here
because the causal claim outlives the change itself.

## 1. What changed

`case_study/RiscvPmp/Base.v`, three events becoming four:

```coq
Inductive LeakEvent : Set :=
| LeakPc       : Addr -> LeakEvent
| LeakMemRead  : Addr -> LeakEvent
| LeakMemWrite : Addr -> LeakEvent
| LeakMul      : bv xlenbits -> bv xlenbits -> LeakEvent   (* NEW *)
```

with `KLeakMul` in `LeakEventConstructor`, the `Finite` enum, and

```coq
unionk_ty leak_event KLeakMul := ty.prod (ty.bvec xlenbits) (ty.bvec xlenbits)
```

plus the two fold/unfold arms. `case_study/RiscvPmp/Machine.v`, one emit site
in `fun_execute_MUL`, after the operand reads and before the product:

```coq
stm_foreign leak [exp_union leak_event KLeakMul
                    (exp_binop bop.pair rs1_val rs2_val)];;
```

The justification is a variable-latency multiplier: a multiplication's timing
depends on its inputs, so an attacker observes them.

**Both operands travel in ONE event, not two.** The alternative — a
single-operand `LeakMulArg` emitted twice — is observationally equally strong
(trace order pins which operand is which) and reuses the `LeakPc`/`LeakMemRead`
code path verbatim. The pair was chosen because it is the more faithful
statement: one multiplication is one observation.

`fun_execute_MUL` is the body of the whole `MUL`/`MULH`/`MULHU`/`MULHSU`
family — `high`/`signed1`/`signed2` only change how the product is
interpreted, not what is fed in — so one emit site covers all four.

## 2. Blast radius: smaller than expected

| layer | file(s) | change needed |
|---|---|---|
| core framework | all of `theories/` | **none** |
| machine model | `Base.v`, `Machine.v` | the above |
| CFGVer light branch | `Spec`, `Verifier`, `Tables`, `Contracts`, `GenContract` | **none** |
| CFGVer heavy branch | `SpecIris`, `VerifierRel`, `TablesRel`, `Adequacy`, `EndToEnd` | **none** |
| binary Iris model | `IrisModelBinary`, `IrisInstanceBinary`, `ModelBinary` | **none** |
| examples | 18 pre-existing end theorems | **none** |

Two reasons it is this contained. Nothing downstream pattern-matches
`LeakEvent` exhaustively — `grep` for the constructors finds hits only in
`Base.v` and the three pre-existing emit sites. And the leak contract is
already generic in the event:

```coq
Definition sep_contract_leak : SepContractFunX leak :=       (* CFGVer/Spec.v *)
  {| sep_contract_logic_variables := ["leak" :: ty_leak_event];
     sep_contract_localstore      := [term_var "leak"];
     sep_contract_precondition    := asn_inv_leakage ∗ secLeakvar "leak"; ... |}
```

`secLeakvar "leak"` demands publicness of *whatever the event carries*, so a
new constructor inherits the whole assertion, refinement and adequacy chain
with no per-constructor case anywhere.

The `typedefkit` fold/unfold obligations (`Base.v:915`) absorb a `ty.prod`
payload unchanged: they are `abstract (intros [] [[] x]; repeat destruct on
unit/prod; auto)`, and the `prod` arm was already there for
`fetch_result`'s `KF_Error`.

## 3. The prediction that was wrong

**Predicted:** the pair payload would need a fix in `theories/Symbolic/Solver.v`.
The reasoning: `simplify_secLeak` (`Solver.v:2250`) recurses through
`term_binop` and `term_unop`, but its union arm does **not** recurse into the
payload —

```coq
| term_union U K tl => dlist_secLeak tl      (* = singleton (formula_secLeak tl) *)
```

— and `simplify_formula` is applied once per formula. So the assert should
arrive as the single atomic formula `formula_secLeak (term_binop bop.pair x y)`,
which `secLeakT`'s `Term_eqb` lookup can never match against the per-variable
`formula_secLeak (term_var x)` facts that a public `reg_spec` puts in `wco`.
Expected consequence: a spurious residual even for two PUBLIC operands.

**Measured: REFUTED.** The public-operand VC discharges with the unmodified
`vm_compute; solve_vc; solve_symbase_fetch` line, and the residual left by the
*secret* arm is per-operand (§4), not on the pair.

**Mechanism.** `combined_solver` runs `solver_generic` several times
(`Solver.v:3961`), so the `formula_secLeak (bop.pair x y)` that round 1 emits is
re-simplified by round 2 — where it is a `term_binop`, and the `cat` arm splits
it into `secLeak x` and `secLeak y`. The non-recursion in the union arm is
absorbed by the fixpoint, and the `TODO` on that line is a mild inefficiency
(one extra pass), not a correctness gap.

Cost of not checking first: one `theories/`-wide rebuild (~6 min for
`Solver.vo` alone, plus every downstream `.vo`) would have been spent on a
non-problem. The check that settled it was a single 4-line probe.

## 4. The experiment

One axis, two values. Everything else — program, base, fuel, tactic line — is
held fixed.

| axis | values |
|---|---|
| `operand-publicness` | `both-public` \| `one-secret` |
| `emit-site` (control) | `present` \| `disabled` |

Program in all four cells: `MUL X3 X2 X1` at a symbolic base, via
`gen_contract_param`, fuel 5. `Assembly.MUL rd rs1 rs2` = `X3 <- X2 * X1`.

| variant | operand-publicness | emit-site | file | protocol | result |
|---|---|---|---|---|---|
| `both-public + present` | both public | present | `ZZMulLeak.v` | `intros; vm_compute; solve_vc; solve_symbase_fetch` + `Qed` | **VC discharges** |
| `one-secret + present` | X1 secret | present | `ZZMulLeakSecret.v` | identical | **FAILS** |
| `one-secret + disabled` | X1 secret | disabled | `ZZMulLeakSecret.v`, emit line commented out | identical | **VC discharges** |
| `both-public + disabled` | both public | disabled | — | — | not run: implied, the model is strictly weaker |

The protocol column is identical across all rows by construction — the second
and third differ *only* in whether `Machine.v` carries the emit line, which is
why the third row is a control on the change and not on the program.

## 5. Reading it apart

**The failure is the new event, not `MUL` on secret data.** Row 3 is the load-bearing
one. Without it, row 2's failure is equally consistent with some unrelated wall
in `fun_execute_MUL` — `uop.signed`/`uop.unsigned` on a `NonSyncVal`, the
`to_bits` widening, `exp_vector_subrange`. With the emit line disabled and
*nothing else* changed, the same secret-operand program verifies. So the whole
of the gap is `LeakMul`.

**The obligation is per-operand, and only the secret one survives.** The
residual after `solve_vc` on row 2, verbatim:

```
H0 : ... (eformula_secLeak (eterm_var "v.1"))     (* X2, PUBLIC  -- available *)
H1 : ... (eformula_secLeak (eterm_var "p"))       (* the base    -- available *)
|-   ... (eformula_secLeak (eterm_var "v"))       (* X1, SECRET  -- open      *)
```

Three things at once: the pair was decomposed (§3); the public operand's
obligation was discharged from the `reg_spec` fact; and what is left is exactly
one unprovable `secLeak` naming the secret operand. This is the
`NonSyncVal ⇒ False` wall (`secret-data-walls`) doing its job — a secret is
fine as a *value* and fatal as an *observation*.

## 6. What this means

The positive half is a real example, `Example/MulPublic.v` +
`Example/MulPublicResult.v`, registered in `_CoqProject`, `Results.v` and
`gate.sh`'s `AXIOM_CLEAN_THMS`. It is the constant-time table-index idiom —
public index × public element size → public byte offset, then mixed with a
secret by `ADD`:

```
MUL   T0, A0, A1     ; leaks A0, A1 -- both PUBLIC
MULHU T1, A0, A1     ; leaks A0, A1 -- both PUBLIC
ADD   T2, A2, T0     ; A2 SECRET, emits no event
ADD   A3, T2, T1
```

`mul_public_noninterferent_param` is axiom-clean (`pure_decode`, `mmioenv`).
`MUL` and `MULHU` are both present deliberately: two of the four family
members exercise the shared emit site.

The negative half has no theorem, so it stays as the two `ZZ` probes above
rather than becoming a file in the build.

**The general point this establishes.** Adding an observation to this model is
a local edit — one data-type extension plus one emit site — because publicness
is enforced through a single generic `secLeak` assertion on the event rather
than per-event-kind. Anything with the same shape ("instruction X leaks
value V") should cost the same. What it does *not* establish is that a
leakage model needing a NEW KIND of side condition (a *relation* between two
events, say, or an ordering constraint) would be as cheap; nothing here tests
that.

**Known limitation, unchanged by this work.** A secret-dependent *branch* is
still rejected outright rather than analysed, because `formula_bool` /
`formula_relop` map `NonSyncVal` to `False`. `Machine.v`'s `bool_to_bits`
note (§4 there) explains why that is a sound over-approximation and what the
general fix would be. `LeakMul` is orthogonal: it adds an observation the
model previously lacked, it does not widen what the executor can reason about.

## 7. Files / reproduction

Probes (deliberately not in `_CoqProject`, per the `ZZ*.v` convention):

- `Example/ZZMulLeak.v` — `both-public + present`
- `Example/ZZMulLeakSecret.v` — `one-secret + present`

```bash
# rows 1 and 2
make -f Makefile.coq case_study/RiscvPmp/CFGVer/Example/Prelude.vo
coqc $(sed -n 's/^-arg //p' _CoqProject | tr '\n' ' ') \
     -Q case_study/RiscvPmp Katamaran.RiscvPmp -R theories Katamaran \
     case_study/RiscvPmp/CFGVer/Example/ZZMulLeak.v        # succeeds
coqc ... case_study/RiscvPmp/CFGVer/Example/ZZMulLeakSecret.v   # fails

# row 3: the control -- comment out the stm_foreign leak in fun_execute_MUL,
# rebuild the light chain, rerun ZZMulLeakSecret.v (now succeeds), restore.

# to see the residual instead of the failure, drop solve_symbase_fetch and
# read the goal after `intros; vm_compute; solve_vc.`
```

Full regression: `GATE_JOBS=1 ./scripts/gate.sh` (`GATE_JOBS=1` because the
default `-j3` runs three ~3 GB `coqc` processes).
