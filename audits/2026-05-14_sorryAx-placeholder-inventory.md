# `sorryAx` and Explicit Axiom Placeholder Inventory (2026-05-14)

**Status note (2026-05-18, issue #1649).**  Several issue references below were
live when this inventory was written, but were closed in the 2026-05-16/17
proof-debt sweep.  In particular, the former final-theorem and
orthonormalization/projectivization children #1043, #1363, #1369, #1566, and
#1610 are now historical; the live umbrella for any remaining source-statement
bridge debt is #1458, with the current main-induction and self-improvement proof
obligations tracked by #1507, #1503, and #1230.  The degree-zero pasting
obligation formerly tracked by #1622 has been discharged.

**Status note (2026-05-23).**  The 2026-05-18 live-obligation classification is
now historical.  The current `MIPStarRE/LDT/Test/AxiomAudit.lean` records
standard-axiom checks for `mainFormal`, `mainFormal_sourceStatement`,
`mainInduction`, `mainInduction_sourceStatement`, `selfImprovement`,
`selfImprovementInInductionSection`, `ldPasting`,
`sdp_statement_with_slackness`, and the displayed SDP slackness measurement.
Thus the inventory below should be read as a snapshot of former `sorryAx`
dependencies, not as a current list of declarations intentionally allowed to
depend on `sorryAx`.

## Purpose

This note originally recorded the status of `sorryAx` and explicit axiom-like
placeholders for issue #1586.  The distinction remains important:

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

The explicit axiom-declaration audit reported no `axiom` or `constant`
declarations in the active LDT Lean tree after stripping Lean comments and
docstrings.  This means the `sorryAx` occurrences observed at the snapshot were
not separate project axioms; they were the transitive closure of ordinary
tracked `sorry` obligations.  The current axiom-audit file now checks the
formerly listed source-facing routes against the standard Lean axioms.

`MIPStarRE/LDT/Test/AxiomAudit.lean` is the live inventory of paper-facing
declarations whose axiom closure is checked explicitly.  At the original audit
snapshot, several declarations intentionally allowed `sorryAx` because their
proofs still had named obligations.  In the current tree those entries have
been replaced by standard-axiom checks:

- `MIPStarRE.LDT.Test.mainFormal` and the corrected two-space source theorem
  are checked under the documented `k >= 400md` and `0 < k` statement
  corrections.
- `MIPStarRE.LDT.SelfImprovement.selfImprovement` and
  `MIPStarRE.LDT.MainInductionStep.selfImprovementInInductionSection` are
  checked; the former #1515 and #1503 proof holes are historical.
- `MIPStarRE.LDT.MainInductionStep.mainInduction` and the successor theorem
  `mainInductionSuccessorNext_ofSmallErrorConstruction` are checked for the
  corrected large-`k` interface.
- `MIPStarRE.LDT.Pasting.ldPasting` is checked, including the former #1622
  degree-zero branch.
- `MIPStarRE.LDT.SelfImprovement.selfImprovementHelper` and
  `MIPStarRE.LDT.SelfImprovement.sdp_statement_with_slackness` are checked;
  the former #1230 SDP slackness route is discharged.

Several other audited declarations now require only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`.  In particular, the current
audit records that `globalVarianceOfPoints`,
`laplacianSpectralGapOrdered`, `classicalTestSoundness`, and the
orthonormalization completion route do not depend on `sorryAx`.  The public
theorem `MakingMeasurementsProjective.orthonormalization` also no longer
depends on `sorryAx`: PR #1632 restored the paper constant while leaving the
heterogeneous `orthonormalizationMainLemma` as the remaining issue-#1032 direct
proof obligation.

## Verdict

There is no current evidence of an explicit LDT project axiom or constant being
used to hide a proof gap.  The formerly listed `sorryAx` dependencies for the
main induction, final theorem, pasting, SDP, and self-improvement routes have
been discharged rather than hidden behind new bridge, residual, repair,
data-producing, hypotheses-bundle, assumptions-bundle, `axiom`, or `constant`
assumptions.  Future paper-realignment work should preserve the same principle:
an unfinished source theorem should remain a source-faithful statement with a
tracked proof obligation, not be strengthened by a non-paper hypothesis.
