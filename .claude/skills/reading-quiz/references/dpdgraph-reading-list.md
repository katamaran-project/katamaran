# Statement-only dependency graph with coq-dpdgraph

Builds the exact reading list for a trusted statement: every definition its
TYPE depends on. Installed: `coq-dpdgraph 1.0+8.20` in opam switch
`katamaran-8.20` (`dpd2dot`, `dpdusage` on PATH).

## Graph the statement, not the theorem

`Print DependGraph <theorem>` follows the PROOF term — for
`cmovznz4_noninterferent_param` that was 360k lines and 7.5 GB, all of Iris
and the soundness chain. Wrap the statement in a constant instead:

```coq
From Katamaran.RiscvPmp.CFGVer.Example Require Cmovznz4Result.
From dpdgraph Require dpdgraph.
Definition stmt : Prop :=
  ltac:(let T := type of Cmovznz4Result.cmovznz4_noninterferent_param in exact T).
Set DependGraph File "stmt.dpd".
Print DependGraph stmt.
```

Compile in the scratchpad, from the repo root's load path:

```bash
coqc -Q $REPO/case_study/RiscvPmp Katamaran.RiscvPmp -R $REPO/theories Katamaran Stmt.v
```

Needs the target's `.vo` (check it is newer than its `.v`). Cost: ~25 s and
~7 GB RSS — the 7 GB is LOADING the Result file (Iris), not the graph. Never
run two at once on this 14 GB box.

## Filter to project definitions

`path=` is the module path WITHOUT the library prefix:

```bash
grep '^N:' stmt.dpd \
 | sed -E 's/N: [0-9]+ "([^"]*)".*kind=([a-z]+).*path="([^"]*)".*/\3 | \1 | \2/' \
 | grep -E '^(Noninterference|Gen|Tables|Spec|Example|Muladd|CheckScalar|Cmovznz4|UnOps|Variables)'
grep '^N:' stmt.dpd | sed -E 's/.*path="([^"]*)".*/\1/' | sort | uniq -c | sort -rn | head
```

Nodes without a `path=` are Coq core (`nat`, `eq_rect`) — noise. Most nodes
are the machine model (`Base.RiscvPmpBase`, `Base`, `Machine`); that is
honestly part of the trusted base, but not what a reading quiz reads.

## Reference points (2026-10-08)

- `cmovznz4_noninterferent_param`: 3,338 nodes, 44 project-level —
  `Noninterference` (23), `GenContract` (`concretize_reg/mem`,
  `reg/mem_spec_rel`, `param_val`), `Cmovznz4` data, `Tables` register names.
- `muladd_param_noninterferent`: 3,404 nodes; memory goes through
  `GenSegment`'s `data_spec`/`concretize_data` instead of `concretize_mem`,
  and the statement reaches Katamaran's term language (`uop.eval`,
  `uop.evalRel`, `Variables`) and stdpp's `NoDup_dec`.

dpdgraph shows REACHABILITY, not how a definition is used — treat each node
as a question for the quiz, not as a finding.
