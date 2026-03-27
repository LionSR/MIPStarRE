import MIPStarRE.LDT.CommutativityPoints.Defs

/-!
# Section 10 — Theorems

Output structures and theorem statements for commutativity at points.
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

/-- Output package for `thm:commutativity-points`. -/
structure CommutativityPointsStatement (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (_eps _delta gamma : Error) : Prop where
  sampledDiagonalLineConsistency :
    ConsistencyRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (sampledPointMeasurement params strategy)
      (sampledDiagonalLineEvaluation params strategy)
      (restrictedDiagonalLinesConsistencyError params gamma)
  sampledDiagonalLineApproximation :
    StateDependentDistanceRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (sampledPointMeasurement params strategy)
      (sampledDiagonalLineEvaluation params strategy)
      (pointDiagonalLineApproxError params gamma)
  orderedLiftToMixedBridge :
    StateDependentDistanceRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (pointDiagonalLineMixedProductLeft params strategy)
      (pointDiagonalLineApproxError params gamma)
  orderedLiftToLineBridge :
    StateDependentDistanceRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointDiagonalLineMixedProductLeft params strategy)
      (diagonalLineProductOrdered params strategy)
      (pointDiagonalLineApproxError params gamma)
  diagonalLineProjectiveSwap :
    StateDependentDistanceRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (diagonalLineProductReversed params strategy)
      0
  reversedDropFromLineBridge :
    StateDependentDistanceRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductReversed params strategy)
      (pointDiagonalLineMixedProductRight params strategy)
      (pointDiagonalLineApproxError params gamma)
  reversedDropToPointsBridge :
    StateDependentDistanceRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointDiagonalLineMixedProductRight params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma)
  pointwiseCommutation :
    StateDependentDistanceRel strategy.state
      (uniformDistribution (PointPairQuestion params))
      (pointMeasurementProductLeft params strategy)
      (pointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma)

/-- `thm:commutativity-points`. -/
theorem commutativityPoints
    (params : Parameters)
    (strategy : SymmetricStrategy params d)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    CommutativityPointsStatement params strategy eps delta gamma := by
  sorry

end MIPStarRE.LDT.CommutativityPoints
