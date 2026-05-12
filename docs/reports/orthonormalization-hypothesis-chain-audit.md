# Orthonormalization Obligation Chain Audit

**Issue:** #1359
**Original audit date:** 2026-05-07
**Revised:** 2026-05-12
**Scope:** `MakingMeasurementsProjective/Orthonormalization.lean` through
`SelfImprovement`, `MainInductionStep`, and `Test/MainTheorem/MainFormal.lean`.

This note replaces the obsolete 2026-05-07 description of the old
conditional route into the final theorem.  The current `mainFormal` statement
is source-facing: it has no non-paper proof-obligation input in its public
theorem statement.  The remaining work is recorded as internal proof
obligations.

## Current Verdict

The role-level orthonormalization input that used to feed `mainFormal` has been
removed.  The final theorem no longer asks for the former role-level
orthonormalization input record, nor for explicit left/right
`LeftLiftedProjectivizationRepairInput` fields at the role residual.  Instead,
`MainFormalPostRolePackageDiagonalOrthonormalizationResidual.nonempty_ofDiagonalConsistency`
derives the pre-completion projective submeasurements directly from the
line-130 cross consistency using
`MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency_from_projectivizationRepair`.

The remaining `mainFormal` proof debt is narrower:

1. The successor branch still has the internal obligation
   `mainFormalSuccessorProjectiveCompletionObligation`.
2. The base branch still has the internal obligation
   `mainFormalBaseBranchCompletionObligations_ofBaseCase`.
3. These obligations are not public inputs to `mainFormal`.

Thus #1359 is no longer a warning that the paper theorem has an
orthonormalization-input assumption.  It is now an audit record explaining which
orthonormalization obligations were discharged and which analytic obligations
remain.

## Layer 1: Section 5 Orthonormalization

`MakingMeasurementsProjective.OrthonormalizationInput` still exists as the
general Section 5 interface for the internal theorem
`orthonormalization`.  It consists of a spectral-truncation input and a
locality-preserving repair input for the option-completed measurement.

This is a conditional internal interface, not the paper-facing endpoint used by
`mainFormal`.

The source-facing wrapper used by the final theorem route is
`orthonormalizationMeasurement_of_consistency_from_projectivizationRepair`.
Its public assumptions are the cross-consistency relation, normalization,
finite-type instances, and the nonnegative error boundary.  It invokes the
Section 5 repair construction internally and returns the projective
submeasurement and SDD closeness required by the line-130 construction.

## Layer 2: Section 9 Self-Improvement

`SelfImprovement.OrthonormalizationInput` remains a real proof obligation for
the source-facing self-improvement theorem.  It is obtained from:

- `OrthonormalizationSpectralObligation`, whose source-almost-projective route
  is proved; and
- `OrthonormalizationRepairObligation`, the locality-preserving repair slice
  for the option-completed helper submeasurement.

The current naming makes this status explicit.  The open repair and final-field
work belongs to the self-improvement proof obligations #1514 and #1515, not to
the public statement of `mainFormal`.

## Layer 3: Section 6 Induction

`selfImprovementInInductionSection` and the slice assembly records consume
Section 9 obligations.  They should not be read as additional assumptions of
the paper theorem.  The open Section 6 obligation is to construct the per-slice
induction data and self-improvement data from the recursive induction
hypothesis and the restricted strategies.

This is tracked by #1503 and #1507.

## Layer 4: Final `mainFormal` Assembly

The current final assembly has two explicit internal obligations.

### Successor Branch

`mainFormalSuccessorProjectiveCompletionObligation` must construct a
`MainFormalCascadeRolePackageResidualProjectiveCompletionResidual` in the
non-base case.  The missing ingredients are:

- recursive slice witnesses for the predecessor;
- the corresponding per-slice self-improvement obligations;
- a role residual obtained through the Section 6 successor constructors; and
- the completion and match-mass data needed after the line-130
  orthonormalization residual has been derived.

This is tracked by #1363.

### Base Branch

`mainFormalBaseBranchCompletionObligations_ofBaseCase` must construct the
base-case match-mass preservation data for the orthonormalized submeasurements.
The distinguished completion outcome is already fixed by the
`MainFormalBaseCompletionObligations` to
`MainFormalBaseProjectiveCompletionObligations` conversion.  The remaining
content is the paper's match-mass preservation argument, not diagonal
self-consistency.

This is tracked by #1043 and #1359.

## What Was Discharged

- The final assembly no longer depends on the obsolete conditional route.
- The role-level orthonormalization input record has been removed.
- The line-130 projective submeasurements are produced from cross consistency
  by the Section 5 repair construction.
- Blueprint and documentation now describe these objects as obligations rather
  than as acceptable theorem assumptions.

## What Remains Open

- The Section 9 locality-preserving repair obligation for helper
  submeasurements remains part of the self-improvement proof frontier.
- The source-facing `selfImprovementHelper`, `selfImprovement`,
  `selfImprovementInInductionSection`, and `mainInduction` proofs still contain
  tracked `sorry` obligations.
- The final `mainFormal` proof still depends on the two internal obligation
  declarations named above.

None of these remaining obligations should be added to the public statement of
any theorem labelled by the paper.  They should be proved internally or left as
tracked proof obligations with source-origin documentation.
