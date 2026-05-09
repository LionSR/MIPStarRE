import MIPStarRE.LDT.Test.MainTheorem.OrthonormalizationData

/-!
# Orthonormalization input producer from role residual

This file bridges the Section 6 role residual to the line-130 orthonormalization
inputs consumed by `mainFormal`.  The combining lemma that packages these into
the full `MainFormalBaseRepairedBridgeHypotheses` lives in `MainFormal.lean`
(where that structure is defined).

## What's proved

* `MainFormalPostRolePackageDiagonalOrthonormalizationInput.ofRoleResidual` —
  the orthonormalization input is derivable from the role residual once the two
  locality-preserving repair witnesses are supplied.

## What's not derivable from the role residual alone

* **Diagonal self-consistency** (`MainFormalPostRolePackageDiagonalConsistencyInput`):
  the structure requires `ConsRel G^A G^A ζ₁` and `ConsRel G^B G^B ζ₁` (each POVM
  with itself).  The role residual's `diagonalConsistency` gives cross consistency
  `ConsRel G^A G^B ζ₁` (the two POVMs with each other), which is a different type.
  Diagonal self-consistency is therefore a **separate hypothesis** that must be
  supplied alongside the repair witnesses when constructing `hbaseBridge`.

* **Locality-preserving repair**: the `LeftLiftedProjectivizationRepairInput`
  parameters require QXP-layer data (a `QXPLayerData` with a projective `P`
  family close to the source `G` family), which is the output of Section 9
  (self-improvement).  Until the self-improvement theorem is applied at the
  current level, these are honest hypotheses.

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

/-- Produce the orthonormalization input from a role residual and the two
locality-preserving repair witnesses.

The spectral-truncation fields are supplied by
`spectralTruncationInput_of_sourceAlmostProjective` (via `ofRepairInputs`).
The remaining two fields are the `leftRepair` and `rightRepair` parameters —
these are `LeftLiftedProjectivizationRepairInput` for the unsymmetrized POVMs and
require QXP-layer data from Section 9.

Once those repair witnesses are available, this lemma gives the full
`MainFormalPostRolePackageDiagonalOrthonormalizationInput` needed by the
line-130 orthonormalization wrapper
(`MainFormalPostRolePackageDiagonalOrthonormalizationResidual.nonempty_ofDiagonalInputs`). -/
noncomputable def ofRoleResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (leftRepair :
      LeftLiftedProjectivizationRepairInput strategy.state
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        (consistencyToAlmostProjectiveError scalars.zeta1))
    (rightRepair :
      LeftLiftedProjectivizationRepairInput strategy.state
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        (consistencyToAlmostProjectiveError scalars.zeta1)) :
    MainFormalPostRolePackageDiagonalOrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars) :=
  MainFormalPostRolePackageDiagonalOrthonormalizationInput.ofRepairInputs
    leftRepair rightRepair

end MainFormalPostRolePackageDiagonalOrthonormalizationInput

end Test

end MIPStarRE.LDT
