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
variance-transfer statements.

The local measurement families live on a single prover space `space`, while the
ambient state lives on the bipartite tensor product `space ⊗ space`. This
matches the paper's convention that point and line operators act on the left
register and polynomial weights act on the right register. -/
structure MatrixVarianceTransferRealization (params : Parameters) [FieldModel params.q] where
  /-- The local finite-dimensional Hilbert space carrying the point/line measurements. -/
  space : FiniteHilbertSpace.{0}
  /-- The ambient bipartite positive matrix state. -/
  state : PositiveMatrixState (tensorHilbertSpace space space)
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

/-- The local operator `G_g`. -/
def matrixPolynomialWeightOperator (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : MatrixOperator model.space :=
  model.polynomialMeasurement.effect g

private noncomputable def matrixPolynomialWeightSqrtOperatorCore
    (params : Parameters) [FieldModel params.q]
    {d : Type*} [Fintype d] [DecidableEq d]
    (G : MIPStarRE.Quantum.Submeasurement (DegreeBoundedPolynomialAnswer params) d)
    (g : Polynomial params) : MIPStarRE.Quantum.Op d :=
  CFC.sqrt (G.effect g)

/-- The actual matrix square root `(G_g)^{1/2}` on the local register. -/
noncomputable def matrixPolynomialWeightSqrtOperator (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : MatrixOperator model.space :=
  let _ : Fintype model.space.carrier := model.space.instFintype
  let _ : DecidableEq model.space.carrier := model.space.instDecidableEq
  matrixPolynomialWeightSqrtOperatorCore params model.polynomialMeasurement g

/-- The right-register tensor factor `I ⊗ (G_g)^{1/2}` used to weight the bipartite state. -/
noncomputable def matrixPolynomialWeightRightTensorOperator
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : MatrixOperator (tensorHilbertSpace model.space model.space) :=
  matrixTensorOperator (1 : MatrixOperator model.space)
    (matrixPolynomialWeightSqrtOperator params model g)

/-- The weighted bipartite state `ρ_g = (I ⊗ (G_g)^{1/2}) ρ (I ⊗ (G_g)^{1/2})†`. -/
noncomputable def matrixWeightedPolynomialState (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : PositiveMatrixState (tensorHilbertSpace model.space model.space) :=
  let W := matrixPolynomialWeightRightTensorOperator params model g
  { matrix := W * model.state.matrix * Wᴴ
    positive :=
      by
        simpa [Matrix.star_eq_conjTranspose] using
          star_right_conjugate_nonneg model.state.positive W }

/-- The local operator `A^u_{g(u)}`. -/
noncomputable def matrixPointConditionedOutcomeOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) (u : Point params) : MatrixOperator model.space :=
  (model.pointMeasurement u).effect (g u)

/-- The lifted operator `A^u_{g(u)} ⊗ I` on the bipartite space. -/
noncomputable def matrixLiftedPointConditionedOperatorAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) (u : Point params) :
    MatrixOperator (tensorHilbertSpace model.space model.space) :=
  matrixTensorOperator (matrixPointConditionedOutcomeOperatorAtPolynomial params model g u)
    (1 : MatrixOperator model.space)

/-- The weighted operator `A^u_{g(u)} ⊗ (G_g)^{1/2}` on the bipartite space. -/
noncomputable def matrixWeightedPointConditionedOperatorAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) (u : Point params) :
    MatrixOperator (tensorHilbertSpace model.space model.space) :=
  matrixTensorOperator (matrixPointConditionedOutcomeOperatorAtPolynomial params model g u)
    (matrixPolynomialWeightSqrtOperator params model g)

/-- The matrix realization of the family `u ↦ A^u_{g(u)}` acting on the weighted state `ρ_g`. -/
noncomputable def matrixPointConditionedRealizationAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : MatrixOperatorFamilyRealization params where
  space := tensorHilbertSpace model.space model.space
  state := matrixWeightedPolynomialState params model g
  family := matrixLiftedPointConditionedOperatorAtPolynomial params model g

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

/-- The local event operator `[f(u) = g(u)]`. -/
noncomputable def matrixGeneralizeBLeftOperatorAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MatrixOperator model.space :=
  let valueFamily :=
    MIPStarRE.Quantum.Submeasurement.postprocess (M := model.axisMeasurement qu.1)
      (fun f => f (model.axisQuestionParameter qu))
  valueFamily.effect (g qu.2)

/-- The local event operator `[f = g|_ℓ]`. -/
noncomputable def matrixGeneralizeBRightOperatorAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MatrixOperator model.space :=
  (model.axisMeasurement qu.1).effect
    (Polynomial.restrictToAxisParallelLine params g qu.1)

/-- The weighted left operator in the matrix-level `generalize-b` estimate,
realized as `B^ℓ_{[f(u)=g(u)]} ⊗ (G_g)^{1/2}`. -/
noncomputable def matrixWeightedGeneralizeBLeftOperatorAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    MatrixOperator (tensorHilbertSpace model.space model.space) :=
  matrixTensorOperator (matrixGeneralizeBLeftOperatorAtPolynomial params model g qu)
    (matrixPolynomialWeightSqrtOperator params model g)

/-- The weighted right operator in the matrix-level `generalize-b` estimate,
realized as `B^ℓ_{[f = g|_ℓ]} ⊗ (G_g)^{1/2}`. -/
noncomputable def matrixWeightedGeneralizeBRightOperatorAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    MatrixOperator (tensorHilbertSpace model.space model.space) :=
  matrixTensorOperator (matrixGeneralizeBRightOperatorAtPolynomial params model g qu)
    (matrixPolynomialWeightSqrtOperator params model g)

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

/-- The edgewise squared-norm expression corresponding to the matrix local-variance
comparison for a fixed polynomial. This keeps the original state `ρ` and moves
`(G_g)^{1/2}` into the operators, matching `eq:equivalent-local-variance` in the paper. -/
noncomputable def matrixLocalVarianceDeviationAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  avgOver (rerandomizeCoord params) (fun uv =>
    matrixSquaredDifferenceExpectation model.state
      (matrixWeightedPointConditionedOperatorAtPolynomial params model g uv.1)
      (matrixWeightedPointConditionedOperatorAtPolynomial params model g uv.2))

/-- The independently sampled squared-norm expression corresponding to the matrix
global-variance comparison for a fixed polynomial. -/
noncomputable def matrixGlobalVarianceDeviationAtPolynomial
    (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params)
    (g : Polynomial params) : Error :=
  avgOver (independentPointPair params) (fun uv =>
    matrixSquaredDifferenceExpectation model.state
      (matrixWeightedPointConditionedOperatorAtPolynomial params model g uv.1)
      (matrixWeightedPointConditionedOperatorAtPolynomial params model g uv.2))

/-! ## Matrix statement packages -/

/-- Paper origin: `references/ldt-paper/expansion.tex:273-291`
(`\label{lem:generalize-b}`); matrix realization of the abstract
`GeneralizeBStatement`.

Matrix-level version of `lem:generalize-b`. -/
structure MatrixGeneralizeBStatement (params : Parameters) [FieldModel params.q]
    (model : MatrixVarianceTransferRealization params) : Prop where
  /-- Each fixed polynomial satisfies the claimed matrix deviation bound. -/
  pointwiseDeviationBound :
    ∀ g : Polynomial params,
      matrixGeneralizeBDeviationAtPolynomial params model g ≤ generalizeBError params
  /-- The polynomial average of the matrix deviations satisfies the same bound. -/
  averagedDeviationBound :
    matrixGeneralizeBDeviation params model ≤ generalizeBError params

/-- Paper origin: `references/ldt-paper/expansion.tex:292-324`
(`\label{lem:local-variance-of-points}`); matrix realization of the abstract
`LocalVarianceOfPointsStatement`.

Matrix-level version of `lem:local-variance-of-points`. -/
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

/-- Paper origin: `references/ldt-paper/expansion.tex:325-353`
(`\label{lem:global-variance-of-points}`); matrix realization of the abstract
`GlobalVarianceOfPointsStatement`.

Matrix-level version of `lem:global-variance-of-points`. -/
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
