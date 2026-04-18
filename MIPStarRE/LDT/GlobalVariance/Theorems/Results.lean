import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results
import MIPStarRE.LDT.GlobalVariance.MatrixRealization
import MIPStarRE.LDT.GlobalVariance.Theorems.Averaging
import MIPStarRE.LDT.GlobalVariance.Theorems.Statements

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma pointConditionedExpansionTransfer
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
      (params.m : Error) * pointConditionedLocalVarianceAtPolynomial params strategy G g := by
  simpa [pointConditionedGlobalVarianceAtPolynomial,
    pointConditionedLocalVarianceAtPolynomial] using
      (localToGlobal params
        (fun u =>
          leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
        (weightedPolynomialState params strategy G g))

private lemma matrixPointConditionedExpansionTransfer
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) :
    matrixPointConditionedGlobalVarianceAtPolynomial params model g ≤
      (params.m : Error) * matrixPointConditionedLocalVarianceAtPolynomial params model g := by
  simpa [matrixPointConditionedGlobalVarianceAtPolynomial,
    matrixPointConditionedLocalVarianceAtPolynomial] using
      (matrixLocalToGlobal params
        (matrixPointConditionedRealizationAtPolynomial params model g))

private lemma globalVarianceOfPoints_bound_of_local
    (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error)
    (globalVariance localVariance : Polynomial params → Error)
    (hexpansion :
      ∀ g : Polynomial params,
        globalVariance g ≤ (params.m : Error) * localVariance g)
    (hlocal :
      ∀ g : Polynomial params,
        localVariance g ≤ localVarianceOfPointsError params eps delta) :
    ∀ g : Polynomial params,
      globalVariance g ≤ globalVarianceOfPointsError params eps delta := by
  intro g
  calc
    globalVariance g ≤ (params.m : Error) * localVariance g :=
      hexpansion g
    _ ≤ (params.m : Error) * localVarianceOfPointsError params eps delta := by
      exact mul_le_mul_of_nonneg_left (hlocal g) (by positivity)
    _ = globalVarianceOfPointsError params eps delta := by
      simp [globalVarianceOfPointsError, localVarianceOfPointsError]
      ring

private lemma matrixGeneralizeB_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (hpoint :
      ∀ g : Polynomial params,
        matrixGeneralizeBDeviationAtPolynomial params model g ≤ generalizeBError params) :
    MatrixGeneralizeBStatement params model := by
  refine
    { pointwiseDeviationBound := hpoint
      averagedDeviationBound := by
        simpa [matrixGeneralizeBDeviation] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => matrixGeneralizeBDeviationAtPolynomial params model g)
            (generalizeBError params) hpoint }

private lemma matrixLocalVarianceOfPoints_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error)
    (hpoint :
      ∀ g : Polynomial params,
        matrixPointConditionedLocalVarianceAtPolynomial params model g ≤
          localVarianceOfPointsError params eps delta) :
    MatrixLocalVarianceOfPointsStatement params model eps delta := by
  refine
    { pointwiseLocalVarianceBound := hpoint
      averagedLocalVarianceBound := by
        simpa [matrixPointConditionedLocalVariance] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => matrixPointConditionedLocalVarianceAtPolynomial params model g)
            (localVarianceOfPointsError params eps delta) hpoint }

private lemma matrixGlobalVarianceOfPoints_from_local
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error)
    (hlocal : MatrixLocalVarianceOfPointsStatement params model eps delta) :
    MatrixGlobalVarianceOfPointsStatement params model eps delta := by
  have hexpansion :
      ∀ g : Polynomial params,
        matrixPointConditionedGlobalVarianceAtPolynomial params model g ≤
          (params.m : Error) *
            matrixPointConditionedLocalVarianceAtPolynomial params model g :=
    matrixPointConditionedExpansionTransfer params model
  have hglobal :
      ∀ g : Polynomial params,
        matrixPointConditionedGlobalVarianceAtPolynomial params model g ≤
          globalVarianceOfPointsError params eps delta :=
    globalVarianceOfPoints_bound_of_local params eps delta
      (fun g => matrixPointConditionedGlobalVarianceAtPolynomial params model g)
      (fun g => matrixPointConditionedLocalVarianceAtPolynomial params model g)
      hexpansion hlocal.pointwiseLocalVarianceBound
  refine
    { pointwiseExpansionTransfer := hexpansion
      pointwiseGlobalVarianceBound := hglobal
      averagedGlobalVarianceBound := ?_ }
  · simpa [matrixPointConditionedGlobalVariance] using
      avgOver_polynomialDistribution_le_of_pointwise params
        (fun g => matrixPointConditionedGlobalVarianceAtPolynomial params model g)
        (globalVarianceOfPointsError params eps delta) hglobal

/-! ## Abstract theorem wrappers -/

/-- `lem:generalize-b`. -/
lemma generalizeB
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (_eps _delta _gamma : Error)
    (_hgood : strategy.IsGood _eps _delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params) :
    GeneralizeBStatement params strategy ψbi G := by
  -- The analytic pointwise estimate is an explicit input here. In the
  -- self-improvement pipeline it is supplied by `SelfImprovementBridgePackage`.
  refine
    { aggregateFamilyComparison := by
        exact sddRel_unit_family_of_pointwise ψbi
          (axisParallelLineQuestionDistribution params)
          (generalizeBLeftFamily params strategy G)
          (generalizeBRightFamily params strategy G)
          (fun qu g =>
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
          (fun qu g =>
            weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)
          (by
            intro qu
            simp [generalizeBLeftFamily])
          (by
            intro qu
            simp [generalizeBRightFamily])
          (generalizeBError params) (by
            intro g
            simpa [generalizeBDeviationAtPolynomial] using hpoint g)
      pointwiseNormBound := hpoint
      averagedNormBound := by
        simpa [generalizeBDeviation] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => generalizeBDeviationAtPolynomial params strategy ψbi G g)
            (generalizeBError params) hpoint }

/-- `lem:local-variance-of-points`. -/
lemma localVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta _gamma : Error)
    (_hgood : strategy.IsGood eps delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hedge :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy ψbi G g ≤
          localVarianceOfPointsError params eps delta)
    (hlocal :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta) :
    LocalVarianceOfPointsStatement params strategy ψbi G eps delta := by
  refine
    { aggregateEdgeComparison := by
        exact sddRel_unit_family_of_pointwise ψbi
          (rerandomizeCoord params)
          (localVarianceLeftFamily params strategy G)
          (localVarianceRightFamily params strategy G)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
          (by
            intro uv
            simp [localVarianceLeftFamily])
          (by
            intro uv
            simp [localVarianceRightFamily])
          (localVarianceOfPointsError params eps delta) (by
            intro g
            simpa [localVarianceDeviationAtPolynomial] using hedge g)
      pointwiseEdgeNormBound := hedge
      pointwiseLocalVarianceBound := hlocal
      averagedLocalVarianceBound := by
        simpa [pointConditionedLocalVariance] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)
            (localVarianceOfPointsError params eps delta) hlocal }

/-- `lem:global-variance-of-points`.
Depends on `localVarianceOfPoints` through explicit pointwise local-variance
inputs. `localToGlobal` lifts pointwise local bounds to global bounds, and the
averaging step is fully proved. -/
lemma globalVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hlocalDev :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy ψbi G g ≤
          localVarianceOfPointsError params eps delta)
    (hlocalVar :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta)
    (hdev :
      ∀ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy ψbi G g ≤
          globalVarianceOfPointsError params eps delta) :
    GlobalVarianceOfPointsStatement params strategy ψbi G eps delta := by
  let hlocal :=
    localVarianceOfPoints params strategy eps delta gamma hgood G ψbi hlocalDev hlocalVar
  have hglobal :
      ∀ g : Polynomial params,
        pointConditionedGlobalVarianceAtPolynomial params strategy G g ≤
          globalVarianceOfPointsError params eps delta :=
    globalVarianceOfPoints_bound_of_local params eps delta
      (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)
      (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)
      (pointConditionedExpansionTransfer params strategy G)
      hlocal.pointwiseLocalVarianceBound
  refine
    { aggregateGlobalComparison := by
        exact sddRel_unit_family_of_pointwise ψbi
          (independentPointPair params)
          (globalVarianceLeftFamily params strategy G)
          (globalVarianceRightFamily params strategy G)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
          (fun uv g =>
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
          (by
            intro uv
            simp [globalVarianceLeftFamily, localVarianceLeftFamily])
          (by
            intro uv
            simp [globalVarianceRightFamily, localVarianceRightFamily])
          (globalVarianceOfPointsError params eps delta) (by
            intro g
            simpa [globalVarianceDeviationAtPolynomial] using hdev g)
      pointwiseGlobalNormBound := hdev
      pointwiseExpansionTransfer := pointConditionedExpansionTransfer params strategy G
      pointwiseGlobalVarianceBound := hglobal
      averagedGlobalVarianceBound := by
        simpa [pointConditionedGlobalVariance] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)
            (globalVarianceOfPointsError params eps delta) hglobal }

/-! ## Matrix wrappers -/

/-- Matrix-level counterpart of `lem:generalize-b`, proved by reducing to the
abstract version via an explicit compatibility hypothesis linking the matrix
realization to a `SymStrat`. -/
lemma matrixGeneralizeB
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (strategy : SymStrat params ι)
    (_eps _delta _gamma : Error)
    (_hgood : strategy.IsGood _eps _delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params)
    (hcompat :
      ∀ g : Polynomial params,
        matrixGeneralizeBDeviationAtPolynomial params model g =
          generalizeBDeviationAtPolynomial params strategy ψbi G g) :
    MatrixGeneralizeBStatement params model := by
  refine matrixGeneralizeB_of_pointwise params model ?_
  intro g
  rw [hcompat g]
  exact hpoint g

/-- Matrix-level counterpart of `lem:local-variance-of-points`, proved by reducing
to the abstract version via an explicit compatibility hypothesis linking the
matrix realization to a `SymStrat`. -/
lemma matrixLocalVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (strategy : SymStrat params ι)
    (eps delta _gamma : Error)
    (_hgood : strategy.IsGood eps delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (_ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta)
    (hcompat :
      ∀ g : Polynomial params,
        matrixPointConditionedLocalVarianceAtPolynomial params model g =
          pointConditionedLocalVarianceAtPolynomial params strategy G g) :
    MatrixLocalVarianceOfPointsStatement params model eps delta := by
  refine matrixLocalVarianceOfPoints_of_pointwise params model eps delta ?_
  intro g
  rw [hcompat g]
  exact hpoint g

/-- Matrix-level counterpart of `lem:global-variance-of-points`, proved by
reducing to the abstract version via an explicit compatibility hypothesis
linking the matrix realization to a `SymStrat`. -/
lemma matrixGlobalVarianceOfPoints
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (strategy : SymStrat params ι)
    (eps delta _gamma : Error)
    (_hgood : strategy.IsGood eps delta _gamma)
    (G : SubMeas (Polynomial params) ι)
    (_ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        pointConditionedLocalVarianceAtPolynomial params strategy G g ≤
          localVarianceOfPointsError params eps delta)
    (hcompat :
      ∀ g : Polynomial params,
        matrixPointConditionedLocalVarianceAtPolynomial params model g =
          pointConditionedLocalVarianceAtPolynomial params strategy G g) :
    MatrixGlobalVarianceOfPointsStatement params model eps delta := by
  refine matrixGlobalVarianceOfPoints_from_local params model eps delta ?_
  refine matrixLocalVarianceOfPoints_of_pointwise params model eps delta ?_
  intro g
  rw [hcompat g]
  exact hpoint g

end MIPStarRE.LDT.GlobalVariance
