# Issue #493 conclusion-shaped hypothesis audit (2026-04-26)

Issue #493 forbids replacing a named bridge-package hypothesis with an inline
existential or function hypothesis whose body is already the theorem's
conclusion.  The bridge-package form is still scaffolding, but it is named and
auditable; flattening it into a conclusion-shaped hypothesis hides the same
proof obligation at each call site.

## Low-risk enforcement added

This audit added `scripts/audit_conclusion_shaped_hypotheses.py`, a
report-only heuristic for the PR #491-style inline-existential mutation.  The
script scans Lean theorem/lemma headers, compares explicit existential
hypotheses with existential conclusions, and reports hypotheses that share the
conclusion's salient tokens.

Typical reviewer command:

```bash
python3 scripts/audit_conclusion_shaped_hypotheses.py --ci
```

The `--ci` mode exits non-zero only for unapproved review findings.  It still
prints declarations named like witness adapters (for example `fooOfWitness`) as
`allowed-helper`, because those names accurately advertise that they only
perform monotone witness postprocessing rather than proving a paper theorem.

## Current baseline on `gpt55/issue-493-session30b`

Scan command:

```bash
python3 scripts/audit_conclusion_shaped_hypotheses.py --ci
```

Result:

- scanned Lean theorem/lemma declarations: 1489;
- review findings: 0;
- allowed witness adapters: 1.

The sole allowed helper is:

- `MIPStarRE/LDT/MainInductionStep/Theorems.lean:37`
  `mainInductionOfWitness`, binder `hwitness`.

This is an explicitly named witness adapter: its docstring says it only performs
the final `error ≤ mainInductionError` monotonicity cleanup, and the actual
Section 6 assembly is routed through `mainInductionBaseCase`,
`mainInductionFromPackages`, and `mainInductionByRecursionOnM`.  It is not a
paper theorem name and is therefore materially different from the rejected PR
#491 mutation of `mainInduction` itself.

A separate grep found no live Lean declarations named `*BridgePackage`; the only
remaining Lean occurrence of that string is a historical comment in
`MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction.lean` noting
that the old `ProjectiveNonMeasurementBridgePackage` was removed.

## Limitations

The script is intentionally conservative.  By default it skips existential
hypotheses nested under `∀`, because recursive or stage-wise producers can be
legitimate paper-faithful inputs.  On this baseline, `--include-forall` reports
only the expected Section 6 recursive inputs `mainInductionByRecursionOnM.hrec`
and `mainInductionPublicWrapper.hrec`, both of which quantify over slice
restrictions at dimension `params` while the theorem concludes the successor
case at `params.next`.

Reviewers can still add `--include-forall` for a broader scouting pass when
auditing a suspicious PR.  The script also does not replace the A1 checklist in
`docs/anti_patterns.md`: large conjunctive packages or function hypotheses whose
codomain is conclusion-shaped still require human review against the paper
source.
