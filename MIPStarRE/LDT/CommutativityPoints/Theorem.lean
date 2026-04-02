import MIPStarRE.LDT.CommutativityPoints.Defs

/-!
# Section 10 — Theorems

Output structures and theorem statements for commutativity at points.
The strategy state is bipartite (`QuantumState (ι × ι)`), so all fields
use `strategy.state` directly.
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Output package for `thm:commutativity-points`.

The strategy state is bipartite (`QuantumState (ι × ι)`).  Local-register
fields lift measurements to the left tensor factor. -/
structure CommutativityPointsStatement (params : Parameters)
    (strategy : SymStrat params ι)
    (_eps _delta gamma : Error) : Prop where
  sampledDiagonalLineConsistency :
    ConsRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
      (IdxSubMeas.liftLeft (sampledDiagonalLineEvaluation params strategy))
      (restrictedDiagonalLinesConsistencyError params gamma)
  sampledDiagonalLineApproximation :
    SDDRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
      (IdxSubMeas.liftLeft (sampledDiagonalLineEvaluation params strategy))
      (pointDiagonalLineApproxError params gamma)
  orderedLiftToMixedBridge :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (pointDiagonalLineApproxError params gamma)
  orderedLiftToLineBridge :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (diagonalLineProductOrdered params strategy)
      (pointDiagonalLineApproxError params gamma)
  diagonalLineProjectiveSwap :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (diagonalLineProductReversed params strategy)
      0
  reversedDropFromLineBridge :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductReversed params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma)
  reversedDropToPointsBridge :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma)
  pointwiseCommutation :
    SDDOpRel strategy.state
      (uniformDistribution (PointPairQuestion params))
      (pointMeasurementProductLeft params strategy)
      (pointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma)

/-- `thm:commutativity-points`. -/
theorem commutativityPoints
    (params : Parameters)
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    CommutativityPointsStatement params strategy eps delta gamma := by
  refine
    { sampledDiagonalLineConsistency := by
        /-
        This is the diagonal-lines test, rewritten in the
        `PointDiagonalLineQuestion` indexing used in this section.
        -/
        sorry
      sampledDiagonalLineApproximation := by
        /-
        Apply `prop:simeq-to-approx` to the previous consistency statement.
        -/
        sorry
      orderedLiftToMixedBridge := by
        /-
        First replacement step in the paper:
        `(A^u_a A^v_b) ⊗ I ≈ A^u_a ⊗ L^ℓ_[f(v)=b]`.
        -/
        sorry
      orderedLiftToLineBridge := by
        /-
        Second replacement step:
        `A^u_a ⊗ L^ℓ_[f(v)=b] ≈ I ⊗ (L^ℓ_[f(v)=b] L^ℓ_[f(u)=a])`.
        -/
        sorry
      diagonalLineProjectiveSwap := by
        /-
        The middle exact equality uses projectivity of the diagonal-line
        measurement on the common sampled line.
        -/
        sorry
      reversedDropFromLineBridge := by
        /-
        Third replacement step:
        `I ⊗ (L^ℓ_[f(u)=a] L^ℓ_[f(v)=b]) ≈ A^v_b ⊗ L^ℓ_[f(u)=a]`.
        -/
        sorry
      reversedDropToPointsBridge := by
        /-
        Final replacement step:
        `A^v_b ⊗ L^ℓ_[f(u)=a] ≈ (A^v_b A^u_a) ⊗ I`.
        -/
        sorry
      pointwiseCommutation := by
        /-
        This is the final triangle-inequality assembly of the four
        `≈_{2γm}` steps plus the exact projective swap.
        -/
        sorry }

end MIPStarRE.LDT.CommutativityPoints
