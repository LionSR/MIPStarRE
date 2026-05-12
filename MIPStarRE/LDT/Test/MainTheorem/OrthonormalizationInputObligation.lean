import MIPStarRE.LDT.Test.MainTheorem.OrthonormalizationData

/-!
# Diagonal orthonormalization input from role residual

This file relates the Section 6 role residual to the diagonal orthonormalization
inputs consumed by `mainFormal`.  The combining lemma that assembles these into
the base-case match-mass completion obligation lives in `MainFormal.lean`.

## What's proved

* `MainFormalPostRolePackageDiagonalOrthonormalizationInput.ofRoleResidual` —
  the orthonormalization input is derivable from the role residual once the two
  locality-preserving repair witnesses are supplied.

## What's still not derivable from the role residual alone

* **Match-mass preservation**:
  `MainFormalBaseCompletionObligations` requires the orthonormalized projective
  submeasurements to preserve their match mass against the opposite
  unsymmetrized POVM.  This is the paper-shaped completion route used by the
  base branch of `mainFormal`; it should not be replaced by diagonal
  self-consistency assumptions.

* **Locality-preserving repair**: the `LeftLiftedProjectivizationRepairInput`
  parameters require QXP-layer data (a `QXPLayerData` with a projective `P`
  family close to the source `G` family), which is the output of Section 9
  (self-improvement).  Until the self-improvement theorem is applied at the
  current level, these are explicit proof obligations.

## References

* Issue #1359 — orthonormalization hypothesis chain
* Issue #931 — self-improvement obligations
* Issue #1043 — base-case match-mass completion construction
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder
open MIPStarRE.LDT.MakingMeasurementsProjective

namespace MIPStarRE.LDT

namespace Test

namespace MainFormalPostRolePackageDiagonalOrthonormalizationInput

/-- Produce the orthonormalization input from a role residual and the two
locality-preserving repair witnesses.

Paper origin: `references/ldt-paper/inductive_step.tex:130-149` and
`references/ldt-paper/orthonormalization.tex:273-282`.

The spectral-truncation fields are supplied by
`spectralTruncationInput_of_sourceAlmostProjective` (via `ofRepairInputs`).
The remaining two fields are the `leftRepair` and `rightRepair` parameters —
these are `LeftLiftedProjectivizationRepairInput` for the unsymmetrized POVMs and
require QXP-layer data from Section 9.

Once those repair witnesses are available, this lemma gives the full
`MainFormalPostRolePackageDiagonalOrthonormalizationInput` consumed by the
diagonal orthonormalization construction
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
