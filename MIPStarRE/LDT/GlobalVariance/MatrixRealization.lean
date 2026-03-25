import MIPStarRE.LDT.GlobalVariance.Defs

/-!
# Section 8 — Matrix realization

Concrete finite-dimensional matrix realizations of the variance transfer data.
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder


structure MatrixVarianceTransferRealization (params : Parameters) where
  space : FiniteHilbertSpace
  state : PositiveMatrixState space
  pointMeasurement : Point params → MatrixSubmeasurement (Fq params) space
  axisMeasurement : AxisParallelLine params →
    MatrixSubmeasurement (DegreeBoundedLineAnswer params) space
  polynomialMeasurement :
    MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) space
  axisQuestionParameter : AxisParallelLineQuestion params → Fq params

/-- The concrete operator `G_g`. -/
def matrixPolynomialWeightOperator (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : MatrixOperator model.space :=
  model.polynomialMeasurement.effect (g : DegreeBoundedPolynomialAnswer params)

/--
The concrete stand-in for `(G_g)^{1/2}`. The source uses the square root; this
placeholder omits it and reuses `G_g` itself.
-/
noncomputable def matrixPolynomialWeightSqrtOperator (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : MatrixOperator model.space :=
  matrixPolynomialWeightOperator params model g

/-- The concrete operator `A^u_{g(u)}`. -/
def matrixPointConditionedOutcomeOperatorAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) (u : Point params) : MatrixOperator model.space :=
  (model.pointMeasurement u).effect (g u)

/-- The weighted operator `A^u_{g(u)} (G_g)^{1/2}` on one ambient matrix algebra. -/
noncomputable def matrixWeightedPointConditionedOperatorAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) (u : Point params) : MatrixOperator model.space :=
  matrixPointConditionedOutcomeOperatorAtPolynomial params model g u *
    matrixPolynomialWeightSqrtOperator params model g

/-- The matrix family attached to a fixed polynomial `g`. -/
noncomputable def matrixPointConditionedRealizationAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : MatrixOperatorFamilyRealization params where
  space := model.space
  state := model.state
  family := matrixWeightedPointConditionedOperatorAtPolynomial params model g

/-- The actual local variance of the conditioned points family at a fixed polynomial. -/
noncomputable def matrixPointConditionedLocalVarianceAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  matrixLocalVariance params (matrixPointConditionedRealizationAtPolynomial params model g)

/-- The actual global variance of the conditioned points family at a fixed polynomial. -/
noncomputable def matrixPointConditionedGlobalVarianceAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  matrixGlobalVariance params (matrixPointConditionedRealizationAtPolynomial params model g)

/-- The polynomial-averaged actual local variance. -/
noncomputable def matrixPointConditionedLocalVariance (params : Parameters)
    (model : MatrixVarianceTransferRealization params) : Error :=
  averageOverDistribution (polynomialDistribution params) (fun g =>
    matrixPointConditionedLocalVarianceAtPolynomial params model g)

/-- The polynomial-averaged actual global variance. -/
noncomputable def matrixPointConditionedGlobalVariance (params : Parameters)
    (model : MatrixVarianceTransferRealization params) : Error :=
  averageOverDistribution (polynomialDistribution params) (fun g =>
    matrixPointConditionedGlobalVarianceAtPolynomial params model g)

/-- The concrete left event operator `[f(u) = g(u)]`. -/
noncomputable def matrixGeneralizeBLeftOperatorAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MatrixOperator model.space :=
  let valueFamily :=
    MIPStarRE.Quantum.Submeasurement.postprocess (M := model.axisMeasurement qu.1)
      (fun f => f (model.axisQuestionParameter qu))
  valueFamily.effect (g qu.2)

/-- The concrete right event operator `[f = g|_ℓ]`. -/
noncomputable def matrixGeneralizeBRightOperatorAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MatrixOperator model.space :=
  (model.axisMeasurement qu.1).effect
    ((Polynomial.restrictToAxisParallelLine params g qu.1 : DegreeBoundedLineAnswer params))

/-- The weighted left operator in the matrix-level `generalize-b` estimate. -/
noncomputable def matrixWeightedGeneralizeBLeftOperatorAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MatrixOperator model.space :=
  matrixGeneralizeBLeftOperatorAtPolynomial params model g qu *
    matrixPolynomialWeightSqrtOperator params model g

/-- The weighted right operator in the matrix-level `generalize-b` estimate. -/
noncomputable def matrixWeightedGeneralizeBRightOperatorAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MatrixOperator model.space :=
  matrixGeneralizeBRightOperatorAtPolynomial params model g qu *
    matrixPolynomialWeightSqrtOperator params model g

/-- The actual squared difference appearing in the matrix-level `generalize-b` estimate. -/
noncomputable def matrixGeneralizeBDeviationAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  averageOverDistribution (axisParallelLineQuestionDistribution params) (fun qu =>
    matrixSquaredDifferenceExpectation model.state
      (matrixWeightedGeneralizeBLeftOperatorAtPolynomial params model g qu)
      (matrixWeightedGeneralizeBRightOperatorAtPolynomial params model g qu))

/-- The polynomial-averaged actual `generalize-b` deviation. -/
noncomputable def matrixGeneralizeBDeviation (params : Parameters)
    (model : MatrixVarianceTransferRealization params) : Error :=
  averageOverDistribution (polynomialDistribution params) (fun g =>
    matrixGeneralizeBDeviationAtPolynomial params model g)

/-- The matrix-level local deviation agrees with the concrete local variance. -/
noncomputable def matrixLocalVarianceDeviationAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  matrixPointConditionedLocalVarianceAtPolynomial params model g

/-- The matrix-level global deviation agrees with the concrete global variance. -/
noncomputable def matrixGlobalVarianceDeviationAtPolynomial (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  matrixPointConditionedGlobalVarianceAtPolynomial params model g

/-- Matrix-level version of `lem:generalize-b`. -/
structure MatrixGeneralizeBStatement (params : Parameters)
    (model : MatrixVarianceTransferRealization params) : Prop where
  pointwiseDeviationBound :
    ∀ g : Polynomial params,
      matrixGeneralizeBDeviationAtPolynomial params model g ≤ generalizeBError params
  averagedDeviationBound :
    matrixGeneralizeBDeviation params model ≤ generalizeBError params

/-- Matrix-level version of `lem:local-variance-of-points`. -/
structure MatrixLocalVarianceOfPointsStatement (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error) : Prop where
  pointwiseLocalVarianceBound :
    ∀ g : Polynomial params,
      matrixPointConditionedLocalVarianceAtPolynomial params model g ≤
        localVarianceOfPointsError params eps delta
  averagedLocalVarianceBound :
    matrixPointConditionedLocalVariance params model ≤
      localVarianceOfPointsError params eps delta

/-- Matrix-level version of `lem:global-variance-of-points`. -/
structure MatrixGlobalVarianceOfPointsStatement (params : Parameters)
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error) : Prop where
  pointwiseExpansionTransfer :
    ∀ g : Polynomial params,
      matrixPointConditionedGlobalVarianceAtPolynomial params model g ≤
        (params.m : Error) *
          matrixPointConditionedLocalVarianceAtPolynomial params model g
  pointwiseGlobalVarianceBound :
    ∀ g : Polynomial params,
      matrixPointConditionedGlobalVarianceAtPolynomial params model g ≤
        globalVarianceOfPointsError params eps delta
  averagedGlobalVarianceBound :
    matrixPointConditionedGlobalVariance params model ≤
      globalVarianceOfPointsError params eps delta


end MIPStarRE.LDT.GlobalVariance
