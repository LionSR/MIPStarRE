import MIPStarRE.LDT.CommutativityPoints.Defs

/-!
# Section 10 — Theorems

Output structures and theorem statements for commutativity at points.
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Output package for `thm:commutativity-points`.

In the bipartite model, the state lives on `d * d` (the tensor product of
two copies of the local Hilbert space of dimension `d`).  The `ψbi`
parameter is this bipartite state; all SDDRel fields use it.
TODO(bipartite): when `SymStrat` gains separate local/bipartite dimensions,
`ψbi` should come from the strategy directly. -/
structure CommutativityPointsStatement (params : Parameters)
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (_eps _delta gamma : Error) : Prop where
  sampledDiagonalLineConsistency :
    ConsRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (sampledPointMeasurement params strategy)
      (sampledDiagonalLineEvaluation params strategy)
      (restrictedDiagonalLinesConsistencyError params gamma)
  sampledDiagonalLineApproximation :
    SDDRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (sampledPointMeasurement params strategy)
      (sampledDiagonalLineEvaluation params strategy)
      (pointDiagonalLineApproxError params gamma)
  orderedLiftToMixedBridge :
    SDDRel ψbi
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (pointDiagonalLineMixedProductLeft params strategy)
      (pointDiagonalLineApproxError params gamma)
  orderedLiftToLineBridge :
    SDDRel ψbi
      (pointPairSharedDiagonalLineDistribution params)
      (pointDiagonalLineMixedProductLeft params strategy)
      (diagonalLineProductOrdered params strategy)
      (pointDiagonalLineApproxError params gamma)
  diagonalLineProjectiveSwap :
    SDDRel ψbi
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (diagonalLineProductReversed params strategy)
      0
  reversedDropFromLineBridge :
    SDDRel ψbi
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductReversed params strategy)
      (pointDiagonalLineMixedProductRight params strategy)
      (pointDiagonalLineApproxError params gamma)
  reversedDropToPointsBridge :
    SDDRel ψbi
      (pointPairSharedDiagonalLineDistribution params)
      (pointDiagonalLineMixedProductRight params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma)
  pointwiseCommutation :
    SDDRel ψbi
      (uniformDistribution (PointPairQuestion params))
      (pointMeasurementProductLeft params strategy)
      (pointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma)

/-- `thm:commutativity-points`.
TODO(bipartite): when `SymStrat` gains bipartite dimensions, `ψbi` should be
derived from the strategy and the hypothesis will bind the two. -/
theorem commutativityPoints
    (params : Parameters)
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    CommutativityPointsStatement params strategy ψbi eps delta gamma := by
  sorry

end MIPStarRE.LDT.CommutativityPoints
