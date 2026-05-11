import MIPStarRE.LDT.Test.MainTheorem.OrthonormalizationData

/-!
# Diagonal orthonormalization input from role residual

This file bridges the Section 6 role residual to the diagonal orthonormalization
inputs consumed by `mainFormal`.  The combining lemma that packages these into
the full `MainFormalBaseRepairedBridgeHypotheses` lives in `MainFormal.lean`
(where that structure is defined).

## What's proved

* `MainFormalPostRolePackageDiagonalOrthonormalizationInput.ofRoleResidual` —
  the orthonormalization input is derivable from the role residual by using the
  closed spectral-truncation theorem and the named Section 5
  rounding-to-projectors theorem.

## What's not derivable from the role residual alone

* **Diagonal self-consistency** (`MainFormalPostRolePackageDiagonalConsistencyInput`):
  the structure requires `ConsRel G^A G^A ζ₁` and `ConsRel G^B G^B ζ₁` (each POVM
  with itself).  The role residual's `diagonalConsistency` gives cross consistency
  `ConsRel G^A G^B ζ₁` (the two POVMs with each other), which is a different type.
  Diagonal self-consistency is therefore a **separate hypothesis** that must be
  supplied alongside the role residual, after the orthonormalization input has
  been derived from the Section 5 rounding-to-projectors theorem.

* **Locality-preserving repair**: the ordinary repair fields are supplied by
  `MakingMeasurementsProjective.leftLiftedProjectivizationRepairProducer`.
  Until the corresponding Section 5 rounding-to-projectors theorem is proved,
  the resulting orthonormalization input carries an open proof obligation.

## References

* Issue #1359 — orthonormalization hypothesis chain
* Issue #931 — self-improvement bridge inputs
* Issue #1043 — base-case bridge construction (`hbaseBridge`)
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT.MakingMeasurementsProjective

namespace MIPStarRE.LDT

namespace Test

namespace MainFormalPostRolePackageDiagonalOrthonormalizationInput

/-- Produce the orthonormalization input from a role residual.

The spectral-truncation fields are supplied by
`spectralTruncationInput_of_sourceAlmostProjective` (via `ofRepairInputs`).
The repair fields are supplied by `leftLiftedProjectivizationRepairProducer`,
the Lean form of the Section 5 rounding-to-projectors theorem.  Thus the
remaining proof obligation is located in Section 5 rather than in the
hypotheses of this construction.  This lemma gives the full
`MainFormalPostRolePackageDiagonalOrthonormalizationInput` consumed by the diagonal
orthonormalization construction
(`MainFormalPostRolePackageDiagonalOrthonormalizationResidual.nonempty_ofDiagonalInputs`). -/
noncomputable def ofRoleResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k) :
    MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars) :=
  MainFormalPostRolePackageDiagonalOrthonormalizationInput.ofRepairInputs
    (leftLiftedProjectivizationRepairProducer strategy.state
      (unsymmetrizedLeftPOVM
        (roleResidual.rolePackage scalars).roleMeasurement)
      (consistencyToAlmostProjectiveError scalars.zeta1))
    (leftLiftedProjectivizationRepairProducer strategy.state
      (unsymmetrizedRightPOVM
        (roleResidual.rolePackage scalars).roleMeasurement)
      (consistencyToAlmostProjectiveError scalars.zeta1))

end MainFormalPostRolePackageDiagonalOrthonormalizationInput

end Test

end MIPStarRE.LDT
