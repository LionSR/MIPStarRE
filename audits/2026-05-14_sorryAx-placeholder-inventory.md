# `sorryAx` and Explicit Axiom Placeholder Inventory (2026-05-14)

## Purpose

This note records the current status of `sorryAx` and explicit axiom-like
placeholders for issue #1586.  The distinction is important:

- `sorryAx` is Lean's kernel-level marker for an ordinary unfinished proof
  written with `sorry`.
- An explicit `axiom` or `constant` declaration is a new ambient assumption.

For paper-facing theorems in the LDT formalization, an unfinished proof should
remain a tracked `sorry` on the source-faithful theorem or on the lowest named
construction theorem.  It should not be replaced by an extra connection
hypothesis, residual data, repair input, or explicit axiom-like declaration.

## Commands

```bash
python3 scripts/audit_lean_axiom_declarations.py --root . --ci
lake env lean MIPStarRE/LDT/Test/AxiomAudit.lean
rg -n "sorryAx|expected.*Axioms|assert_.*axioms" MIPStarRE/LDT -g "*.lean"
```

## Current Findings

The explicit axiom-declaration audit reports no `axiom` or `constant`
declarations in the active LDT Lean tree after stripping Lean comments and
docstrings.  This means the current `sorryAx` occurrences in the LDT proof
audit are not separate project axioms; they are the transitive closure of
ordinary tracked `sorry` obligations.

`MIPStarRE/LDT/Test/AxiomAudit.lean` is the live inventory of paper-facing
declarations whose axiom closure is checked explicitly.  As of this audit, the
following declarations intentionally allow `sorryAx` because their proofs still
have named obligations:

- `MIPStarRE.LDT.Test.mainFormal`: final-theorem construction gaps, tracked by
  #1043, #1363, #1369, #1458, and #1566.
- `MIPStarRE.LDT.MakingMeasurementsProjective.orthonormalization`: issue
  #1032, the paper's sharper projectivization constant.
- `MIPStarRE.LDT.SelfImprovement.selfImprovement`: issue #1515,
  source-facing self-improvement derivation.
- `MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSection`: issue
  #1503, induction-section self-improvement derivation.
- `MIPStarRE.LDT.MainInductionStep.mainInduction`: issue #1507, derivation of
  successor-stage inputs from the paper hypotheses.
- `MIPStarRE.LDT.SelfImprovement.selfImprovementHelper`: transitive dependency
  on issue #1230 through `sdp_statement_with_slackness`.  The former #1514
  helper strong self-consistency estimate is now discharged locally.
- `MIPStarRE.LDT.SelfImprovement.sdp_statement_with_slackness`: issue #1230,
  finite-dimensional SDP strong-duality and slackness proof.

Several other audited declarations now require only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`.  In particular, the current
audit records that `globalVarianceOfPoints`,
`laplacianSpectralGapOrdered`, `classicalTestSoundness`, and the
orthonormalization completion route do not depend on `sorryAx`.

## Verdict

There is no current evidence of an explicit LDT project axiom or constant being
used to hide a proof gap.  The remaining `sorryAx` occurrences are ordinary
tracked proof holes.  The correct repair direction is therefore to discharge
the named proof obligations above, or to keep the corresponding source-faithful
statement with a tracked `sorry` during paper realignment.  It is not acceptable
to remove a `sorryAx` dependency by adding non-paper connection, residual,
repair, data-producing, hypotheses-bundle, assumptions-bundle, `axiom`, or
`constant` assumption.
