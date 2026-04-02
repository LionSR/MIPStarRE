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
  sorry

end MIPStarRE.LDT.CommutativityPoints
