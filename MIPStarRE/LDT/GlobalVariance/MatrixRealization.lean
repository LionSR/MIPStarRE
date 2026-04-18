import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization
import MIPStarRE.LDT.GlobalVariance.Defs.Core
import MIPStarRE.LDT.GlobalVariance.Defs.Operators
import MIPStarRE.LDT.GlobalVariance.Defs.Families

/-!
# Section 8 — Matrix realization

This file packages concrete finite-dimensional matrix realizations of the
variance-transfer constructions from the global-variance chapter.

## References

- `blueprint/src/chapter/ch06_variance.tex`
- `references/ldt-paper/expansion.tex`
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable (params : Parameters) [FieldModel params.q]

/-! ## Matrix realizations -/

/-- Concrete matrix data realizing the operators and distributions used in the
variance-transfer statements. -/
structure MatrixVarianceTransferRealization (params : Parameters) [FieldModel params.q] where
  /-- The finite-dimensional Hilbert space on which the realization lives. -/
  space : FiniteHilbertSpace
  /-- The ambient positive matrix state. -/
  state : PositiveMatrixState space
  /-- The point measurement family `u ↦ A^u`. -/
  pointMeasurement : Point params → MatrixSubmeasurement (Fq params) space
  /-- The axis-parallel line measurement family `ℓ ↦ B^ℓ`. -/
  axisMeasurement : AxisParallelLine params →
    MatrixSubmeasurement (DegreeBoundedLineAnswer params) space
  /-- The polynomial-weight submeasurement `G`. -/
  polynomialMeasurement :
    MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) space
  /-- The affine parameter used to evaluate a queried point on an axis-parallel line. -/
  axisQuestionParameter : AxisParallelLineQuestion params → Fq params :=
    axisParallelLineQuestionParameter

/-! ## Concrete operators and variances -/

/-- The concrete operator `G_g`. -/
def matrixPolynomialWeightOperator (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : MatrixOperator model.space :=
  model.polynomialMeasurement.effect g

/--
The concrete stand-in for `(G_g)^{1/2}`. The source uses the square root; this
placeholder omits it and reuses `G_g` itself.
-/
noncomputable def matrixPolynomialWeightSqrtOperator (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : MatrixOperator model.space :=
  matrixPolynomialWeightOperator params model g

/-- The concrete operator `A^u_{g(u)}`. -/
def matrixPointConditionedOutcomeOperatorAtPolynomial (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) (u : Point params) : MatrixOperator model.space :=
  (model.pointMeasurement u).effect (g u)

/-- The weighted operator `A^u_{g(u)} (G_g)^{1/2}` on one ambient matrix algebra. -/
noncomputable def matrixWeightedPointConditionedOperatorAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) (u : Point params) : MatrixOperator model.space :=
  matrixPointConditionedOutcomeOperatorAtPolynomial params model g u *
    matrixPolynomialWeightSqrtOperator params model g

/-- The matrix family attached to a fixed polynomial `g`. -/
noncomputable def matrixPointConditionedRealizationAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : MatrixOperatorFamilyRealization params where
  space := model.space
  state := model.state
  family := matrixWeightedPointConditionedOperatorAtPolynomial params model g

/-- The actual local variance of the conditioned points family at a fixed polynomial. -/
noncomputable def matrixPointConditionedLocalVarianceAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  matrixLocalVariance params (matrixPointConditionedRealizationAtPolynomial params model g)

/-- The actual global variance of the conditioned points family at a fixed polynomial. -/
noncomputable def matrixPointConditionedGlobalVarianceAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  matrixGlobalVariance params (matrixPointConditionedRealizationAtPolynomial params model g)

/-- The polynomial-averaged actual local variance. -/
noncomputable def matrixPointConditionedLocalVariance
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params) : Error :=
  avgOver (polynomialDistribution params) (fun g =>
    matrixPointConditionedLocalVarianceAtPolynomial params model g)

/-- The polynomial-averaged actual global variance. -/
noncomputable def matrixPointConditionedGlobalVariance
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params) : Error :=
  avgOver (polynomialDistribution params) (fun g =>
    matrixPointConditionedGlobalVarianceAtPolynomial params model g)

/-- The concrete left event operator `[f(u) = g(u)]`. -/
noncomputable def matrixGeneralizeBLeftOperatorAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MatrixOperator model.space :=
  let valueFamily :=
    MIPStarRE.Quantum.Submeasurement.postprocess (M := model.axisMeasurement qu.1)
      (fun f => f (model.axisQuestionParameter qu))
  valueFamily.effect (g qu.2)

/-- The concrete right event operator `[f = g|_ℓ]`. -/
noncomputable def matrixGeneralizeBRightOperatorAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MatrixOperator model.space :=
  (model.axisMeasurement qu.1).effect
    (Polynomial.restrictToAxisParallelLine params g qu.1)

/-- The weighted left operator in the matrix-level `generalize-b` estimate. -/
noncomputable def matrixWeightedGeneralizeBLeftOperatorAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MatrixOperator model.space :=
  matrixGeneralizeBLeftOperatorAtPolynomial params model g qu *
    matrixPolynomialWeightSqrtOperator params model g

/-- The weighted right operator in the matrix-level `generalize-b` estimate. -/
noncomputable def matrixWeightedGeneralizeBRightOperatorAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MatrixOperator model.space :=
  matrixGeneralizeBRightOperatorAtPolynomial params model g qu *
    matrixPolynomialWeightSqrtOperator params model g

/-- The actual squared difference appearing in the matrix-level `generalize-b` estimate. -/
noncomputable def matrixGeneralizeBDeviationAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  avgOver (axisParallelLineQuestionDistribution params) (fun qu =>
    matrixSquaredDifferenceExpectation model.state
      (matrixWeightedGeneralizeBLeftOperatorAtPolynomial params model g qu)
      (matrixWeightedGeneralizeBRightOperatorAtPolynomial params model g qu))

/-- The polynomial-averaged actual `generalize-b` deviation. -/
noncomputable def matrixGeneralizeBDeviation
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params) : Error :=
  avgOver (polynomialDistribution params) (fun g =>
    matrixGeneralizeBDeviationAtPolynomial params model g)

/-- The matrix-level local deviation agrees with the concrete local variance. -/
noncomputable def matrixLocalVarianceDeviationAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  matrixPointConditionedLocalVarianceAtPolynomial params model g

/-- The matrix-level global deviation agrees with the concrete global variance. -/
noncomputable def matrixGlobalVarianceDeviationAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  matrixPointConditionedGlobalVarianceAtPolynomial params model g

/-! ## Matrix statement packages -/

/-- Matrix-level version of `lem:generalize-b`. -/
structure MatrixGeneralizeBStatement (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params) : Prop where
  /-- Each fixed polynomial satisfies the claimed matrix deviation bound. -/
  pointwiseDeviationBound :
    ∀ g : Polynomial params,
      matrixGeneralizeBDeviationAtPolynomial params model g ≤ generalizeBError params
  /-- The polynomial average of the matrix deviations satisfies the same bound. -/
  averagedDeviationBound :
    matrixGeneralizeBDeviation params model ≤ generalizeBError params

/-- Matrix-level version of `lem:local-variance-of-points`. -/
structure MatrixLocalVarianceOfPointsStatement (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error) : Prop where
  /-- Each fixed polynomial satisfies the matrix local-variance bound. -/
  pointwiseLocalVarianceBound :
    ∀ g : Polynomial params,
      matrixPointConditionedLocalVarianceAtPolynomial params model g ≤
        localVarianceOfPointsError params eps delta
  /-- The polynomial average of the matrix local variances satisfies the same bound. -/
  averagedLocalVarianceBound :
    matrixPointConditionedLocalVariance params model ≤
      localVarianceOfPointsError params eps delta

/-- Matrix-level version of `lem:global-variance-of-points`. -/
structure MatrixGlobalVarianceOfPointsStatement (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (eps delta : Error) : Prop where
  /-- Each fixed polynomial satisfies the matrix local-to-global comparison. -/
  pointwiseExpansionTransfer :
    ∀ g : Polynomial params,
      matrixPointConditionedGlobalVarianceAtPolynomial params model g ≤
        (params.m : Error) *
          matrixPointConditionedLocalVarianceAtPolynomial params model g
  /-- Each fixed polynomial satisfies the matrix global-variance bound. -/
  pointwiseGlobalVarianceBound :
    ∀ g : Polynomial params,
      matrixPointConditionedGlobalVarianceAtPolynomial params model g ≤
        globalVarianceOfPointsError params eps delta
  /-- The polynomial average of the matrix global variances satisfies the same bound. -/
  averagedGlobalVarianceBound :
    matrixPointConditionedGlobalVariance params model ≤
      globalVarianceOfPointsError params eps delta


end MIPStarRE.LDT.GlobalVariance
