# Orthonormalization Obligation Chain Audit

**Issue:** #1359
**Original audit date:** 2026-05-07
**Revised:** 2026-05-13
**Scope:** `MakingMeasurementsProjective/Orthonormalization.lean` through
`SelfImprovement`, `MainInductionStep`, and `Test/MainTheorem/MainFormal.lean`.

> **Status note, 2026-05-20.**  This report has been updated to the current
> proof frontier.  The Section 5 orthonormalization route, Section 9
> self-improvement theorem, and induction-section self-improvement wrapper are
> checked without `sorry` or `axiom`.  The former #1514, #1515, and #1503
> proof gaps are historical.  The remaining direct construction proof hole in
> the same-space final-theorem route is the Section 6 small-error successor
> construction
> `MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`
> tracked by #1507.  The source-labelled `thm:main-formal` and
> `thm:main-induction` statements also have named source-boundary obligations,
> respectively `mainFormal_sourceConclusion` and
> `mainInduction_sourceRangeObligation`.
> The final-theorem wrapper proves the saturated-error branch and leaves
> `mainFormal_sourceSmallErrorConclusion` as the remaining direct final
> source-boundary proof hole.
>
> **Status note, 2026-05-22.**  The corrected large-`k` Section 6 successor
> construction is now checked.  The source-boundary obligations above remain:
> the printed source range for `thm:main-induction` and the final two-space
> source theorem.
>
> **Status note, 2026-05-23.**  This report is now historical as a proof-frontier
> inventory.  The corrected large-\(k\), nonzero-sampling source route is
> proof-complete, including the two-space role-register final theorem.  The
> remaining differences from the literal printed paper are documented statement
> corrections: \(k\ge 400md\) in place of the printed \(k\ge md\), and the
> final-theorem boundary \(0<k\).  The older source-range and small-error
> obligation names mentioned below are no longer live Lean declarations.

This note replaces the obsolete 2026-05-07 description of the old conditional
route into the final theorem.  Its body is retained as a dated audit of the
orthonormalization chain; the current source-facing theorem statements no longer
carry non-paper proof-obligation inputs, and the corrected source route has no
live source-range obligation declarations.

## Current Verdict

The role-level orthonormalization input that used to feed `mainFormal` has been
removed.  The final theorem no longer asks for the former role-level
orthonormalization input record, nor for explicit left/right repair-input
fields at the role residual.  Instead,
`MainFormalDiagonalOrthonormalizationWitness.nonempty_ofDiagonalConsistency`
derives the pre-completion projective submeasurements directly from the
line-130 cross consistency using
`MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency_from_projectivizationRepair`.

The former proof debt for the same-space theorem `mainFormal` was transitive
through Section 6.  That Section 6 successor construction is now checked for the
corrected large-\(k\) interface, and the final theorem source-boundary route is
checked under the documented boundary corrections.

Thus #1359 is no longer a warning that the paper theorem has an
orthonormalization-input assumption.  It is now an audit record explaining which
orthonormalization obligations were discharged and why the later Section 6 work,
now checked, was separate from orthonormalization.

## Layer 1: Section 5 Orthonormalization

The former `MakingMeasurementsProjective.OrthonormalizationInput` record has
been removed, as have the older projectivization repair-input abbreviations.
The paper-facing Section 5 statements now keep the missing sharp
orthonormalization construction as tracked proof gaps rather than as an extra
record-valued theorem hypothesis.

The source-facing wrapper used by the final theorem route is
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair`.
Its public assumptions are the cross-consistency relation, normalization,
finite-type instances, and the nonnegative error boundary.  It invokes the
Section 5 repair construction internally and returns the projective
submeasurement and SDD closeness required by the line-130 construction.

## Layer 2: Section 9 Self-Improvement

The former `SelfImprovement.OrthonormalizationInput` bundle has also been
removed.  The later `OrthonormalizationSpectralObligation` abbreviation has now
also been retired: its useful content is the direct construction
`spectralTruncationStatement_of_sourceAlmostProjective`.  The
locality-preserving repair and final-field arguments are no longer presented as
bundled theorem inputs; the source-facing self-improvement theorem now checks
without `sorry` or `axiom`.

## Layer 3: Section 6 Induction

`selfImprovementInInductionSection` and the slice assembly records now call the
source-facing Section 9 theorem directly.  That wrapper is checked.  The open
Section 6 obligation is to construct the answer-valued restricted slice
profile, obtain the predecessor induction conclusion for each restricted
slice, realize the slice-wise self-improvement interface, assemble the pasting
input, and close the scalar estimates in the small-error successor branch.

This is tracked by #1507; #1503 is historical for the current code.

## Layer 4: Final `mainFormal` Assembly

The current final assembly has no explicit orthonormalization hypothesis and no
final-theorem bridge or residual package.  Its remaining proof debt is the
transitive dependency on `MainInductionStep.mainInduction`.

### Successor Branch

The successor branch is now represented by the native Section 6 theorem
`mainInductionSuccessorNext_ofSmallErrorConstruction`.  It must produce the
measurement promised by the small-error successor step from the paper
hypotheses and the recursive predecessor induction argument.

This is tracked by #1507.

### Base Branch

The base branch is checked in the current route.  The older
`mainFormalBaseBranchCompletionObligations_ofBaseCase` entry should be read as
historical audit context.

## What Was Discharged

- The final assembly no longer depends on the obsolete conditional route.
- The role-level orthonormalization input record has been removed.
- The Section 5 and Section 9 bundled orthonormalization input records have
  been removed.
- The line-130 projective submeasurements are produced from cross consistency
  by the Section 5 repair construction.
- Section 9 self-improvement and the induction-section self-improvement wrapper
  are checked without `sorry` or `axiom`.
- Blueprint and documentation now separate the source statements from current
  Lean interfaces where the Lean theorem is not yet the full paper statement.

## What Remains Open

- The Section 6 small-error successor construction
  `mainInductionSuccessorNext_ofSmallErrorConstruction` remains open.
- The source-facing `mainInduction` and current `mainFormal` interface depend
  transitively on that theorem.

None of these remaining obligations should be added to the public statement of
any theorem labelled by the paper.  They should be proved internally or left as
tracked proof obligations with source-origin documentation.
