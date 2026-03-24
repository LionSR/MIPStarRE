import MIPStarRE.LDT.Section8GlobalVariance.MatrixRealization

namespace MIPStarRE.LDT.Section8GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Section5MakingMeasurementsProjective
open MIPStarRE.LDT.Section7ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder


/-- Output package for `lem:generalize-b`. -/
structure GeneralizeBStatement (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) : Prop where
  aggregateFamilyComparison :
    StateDependentDistanceRel strategy.state
      (axisParallelLineQuestionDistribution params)
      (generalizeBLeftFamily params strategy G)
      (generalizeBRightFamily params strategy G)
      (generalizeBError params)
  pointwiseNormBound :
    ∀ g : Polynomial params,
      generalizeBDeviationAtPolynomial params strategy G g ≤ generalizeBError params
  averagedNormBound :
    generalizeBDeviation params strategy G ≤ generalizeBError params

/-- Output package for `lem:local-variance-of-points`. -/
structure LocalVarianceOfPointsStatement (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) (eps delta : Error) : Prop where
  aggregateEdgeComparison :
    StateDependentDistanceRel strategy.state
      (rerandomizeCoord params)
      (localVarianceLeftFamily params strategy G)
      (localVarianceRightFamily params strategy G)
      (localVarianceOfPointsError params eps delta)
  pointwiseEdgeNormBound :
    ∀ g : Polynomial params,
      localVarianceDeviationAtPolynomial params strategy G g ≤
        localVarianceOfPointsError params eps delta
  pointwiseLocalVarianceBound :
    ∀ g : Polynomial params,
      pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
        localVarianceOfPointsError params eps delta
  averagedLocalVarianceBound :
    pointConditionedLocalVariance params strategy G ≤
      localVarianceOfPointsError params eps delta

/-- Output package for `lem:global-variance-of-points`. -/
structure GlobalVarianceOfPointsStatement (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) (eps delta : Error) : Prop where
  aggregateGlobalComparison :
    StateDependentDistanceRel strategy.state
      (independentPointPair params)
      (globalVarianceLeftFamily params strategy G)
      (globalVarianceRightFamily params strategy G)
      (globalVarianceOfPointsError params eps delta)
  pointwiseGlobalNormBound :
    ∀ g : Polynomial params,
      globalVarianceDeviationAtPolynomial params strategy G g ≤
        globalVarianceOfPointsError params eps delta
  pointwiseExpansionTransfer :
    ∀ g : Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        (params.m : Error) *
          pointConditionedLocalVarianceAtPolynomial params strategy G g
  pointwiseGlobalVarianceBound :
    ∀ g : Polynomial params,
      pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
        globalVarianceOfPointsError params eps delta
  averagedGlobalVarianceBound :
    pointConditionedGlobalVariance params strategy G ≤
      globalVarianceOfPointsError params eps delta

lemma matrixGeneralizeB
    (params : Parameters)
    (model : MatrixVarianceTransferRealization params) :
    MatrixGeneralizeBStatement params model := by
  sorry

/-- The concrete matrix-level counterpart of `lem:local-variance-of-points`. -/
lemma matrixLocalVarianceOfPoints
    (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error) :
    MatrixLocalVarianceOfPointsStatement params model eps delta := by
  sorry

/-- The concrete matrix-level counterpart of `lem:global-variance-of-points`. -/
lemma matrixGlobalVarianceOfPoints
    (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error) :
    MatrixGlobalVarianceOfPointsStatement params model eps delta := by
  sorry

/-- `lem:generalize-b`. -/
lemma generalizeB
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeasurement (Polynomial params)) :
    GeneralizeBStatement params strategy G := by
  sorry

/-- `lem:local-variance-of-points`. -/
lemma localVarianceOfPoints
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeasurement (Polynomial params)) :
    LocalVarianceOfPointsStatement params strategy G eps delta := by
  sorry

/-- `lem:global-variance-of-points`. -/
lemma globalVarianceOfPoints
    (params : Parameters)
    (strategy : SymmetricStrategy params)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeasurement (Polynomial params)) :
    GlobalVarianceOfPointsStatement params strategy G eps delta := by
  sorry


end MIPStarRE.LDT.Section8GlobalVariance
