import MIPStarRE.Paper2009LDT.Section7ExpansionHypercubeGraph

/-!
Matching scaffold for Section 8 of the low individual degree paper in
`references/ldt-paper/expansion.tex`.

This file records the named lemmas controlling the global variance of the points
measurements. The declarations now expose the conditioned operators
$A(g)^u = A^u_{g(u)}$, the weighted states $|ψ_g⟩ = (I ⊗ G_g^{1/2})|ψ⟩$, and the
variance-transfer quantities that the paper bounds.
-/

namespace MIPStarRE.Paper2009LDT.Section8GlobalVariance

open MIPStarRE.Paper2009LDT
open MIPStarRE.Paper2009LDT.Section5MakingMeasurementsProjective
open MIPStarRE.Paper2009LDT.Section7ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

abbrev AxisParallelLineQuestion (params : Parameters) :=
  AxisParallelLine params × Point params

abbrev PointPairQuestion (params : Parameters) :=
  Point params × Point params

/-- TODO(degree): polynomial answers should be degree-bounded objects rather than raw functions. -/
abbrev DegreeBoundedPolynomialAnswer (params : Parameters) :=
  Point params → Fq params

/-- TODO(degree): line answers should be degree-bounded objects rather than raw functions. -/
abbrev DegreeBoundedLineAnswer (params : Parameters) :=
  Fq params → Fq params

/-- The distribution of an axis-parallel line together with a point queried on it. -/
def axisParallelLineQuestionDistribution (params : Parameters) :
    Distribution (AxisParallelLineQuestion params) :=
  { name := s!"axisLinePoint({params.m},{params.q},{params.d})" }

/-- A placeholder distribution over low-degree polynomials. -/
def polynomialDistribution (params : Parameters) :
    Distribution (Polynomial params) :=
  { name := s!"poly({params.m},{params.q},{params.d})" }

/-- The operator `G_g` attached to the polynomial outcome `g`. -/
def polynomialWeightOperator (params : Parameters)
    (G : SubMeasurement (Polynomial params)) (g : Polynomial params) : Operator :=
  G.outcomeOperator g

/-- The operator `(G_g)^{1/2}` used throughout `expansion.tex`. -/
noncomputable def polynomialWeightSqrtOperator (params : Parameters)
    (G : SubMeasurement (Polynomial params)) (g : Polynomial params) : Operator :=
  formalSquareRoot (polynomialWeightOperator params G g)

/-- The weighted state `|ψ_g⟩ = (I ⊗ G_g^{1/2}) |ψ⟩`. -/
noncomputable def weightedPolynomialState (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) (g : Polynomial params) : QuantumState :=
  { name :=
      s!"psi_g({strategy.state.name},{(polynomialWeightSqrtOperator params G g).name})" }

/-- The concrete operator `A^u_{g(u)}` for a fixed polynomial `g`. -/
def pointConditionedOutcomeOperatorAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (g : Polynomial params) (u : Point params) : Operator :=
  (strategy.pointMeasurement u).toSubMeasurement.outcomeOperator (g u)

/-- The operator family `u ↦ A(g)^u = A^u_{g(u)}` for a fixed polynomial `g`. -/
def pointConditionedOperatorFamilyAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (g : Polynomial params) : Point params → Operator :=
  fun u => pointConditionedOutcomeOperatorAtPolynomial params strategy g u

/-- The paper's weighted operator `A^u_{g(u)} ⊗ (G_g)^{1/2}`. -/
noncomputable def weightedPointConditionedOperatorAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params))
    (g : Polynomial params) (u : Point params) : Operator :=
  formalTensor
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
    (polynomialWeightSqrtOperator params G g)

/-- The local variance of `A(g)` on the weighted state `|ψ_g⟩`. -/
noncomputable def pointConditionedLocalVarianceAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params))
    (g : Polynomial params) : Error :=
  localVariance params
    (pointConditionedOperatorFamilyAtPolynomial params strategy g)
    (weightedPolynomialState params strategy G g)

/-- The global variance of `A(g)` on the weighted state `|ψ_g⟩`. -/
noncomputable def pointConditionedGlobalVarianceAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params))
    (g : Polynomial params) : Error :=
  globalVariance params
    (pointConditionedOperatorFamilyAtPolynomial params strategy g)
    (weightedPolynomialState params strategy G g)

/-- The polynomial-averaged local variance of the conditioned points family. -/
noncomputable def pointConditionedLocalVariance (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) : Error :=
  averageOverDistribution (polynomialDistribution params)
    (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)

/-- The polynomial-averaged global variance of the conditioned points family. -/
noncomputable def pointConditionedGlobalVariance (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) : Error :=
  averageOverDistribution (polynomialDistribution params)
    (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)

/-- The event operator `B^ℓ_[f(u)=g(u)]`. -/
def generalizeBLeftOperatorAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : Operator :=
  let ℓ := qu.1
  let u := qu.2
  { name :=
      s!"{(strategy.axisParallelMeasurement ℓ).toSubMeasurement.name}[f(\
         {pointCode params u})={(g u).1}]" }

/-- The event operator `B^ℓ_[f = g|_ℓ]`. -/
def generalizeBRightOperatorAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (_g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : Operator :=
  let ℓ := qu.1
  { name := s!"{(strategy.axisParallelMeasurement ℓ).toSubMeasurement.name}[g|ell]" }

/-- The weighted left operator in `lem:generalize-b`. -/
noncomputable def weightedGeneralizeBLeftOperatorAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params))
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : Operator :=
  formalTensor
    (generalizeBLeftOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

/-- The weighted right operator in `lem:generalize-b`. -/
noncomputable def weightedGeneralizeBRightOperatorAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params))
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : Operator :=
  formalTensor
    (generalizeBRightOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

/-- The squared norm expression controlled by `lem:generalize-b` for a fixed `g`. -/
noncomputable def generalizeBDeviationAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params))
    (g : Polynomial params) : Error :=
  averageOverDistribution (axisParallelLineQuestionDistribution params)
    (fun qu =>
      operatorExpectation strategy.state
        (formalSquare
          (formalDifference
            (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
            (weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu))))

/-- The polynomial-averaged deviation controlled by `lem:generalize-b`. -/
noncomputable def generalizeBDeviation (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) : Error :=
  averageOverDistribution (polynomialDistribution params)
    (fun g => generalizeBDeviationAtPolynomial params strategy G g)

/-- Aggregated family for the left-hand side of `lem:generalize-b`. -/
noncomputable def generalizeBLeftFamily (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (AxisParallelLineQuestion params) Unit :=
  fun qu =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
    { name := s!"generalizeB.left({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- Aggregated family for the right-hand side of `lem:generalize-b`. -/
noncomputable def generalizeBRightFamily (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (AxisParallelLineQuestion params) Unit :=
  fun qu =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)
    { name := s!"generalizeB.right({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- Aggregated family for `A^u_[g(u)] ⊗ (G_g)^{1/2}`. -/
noncomputable def localVarianceLeftFamily (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun uv =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
    { name := s!"localVariance.left({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- Aggregated family for `A^v_[g(v)] ⊗ (G_g)^{1/2}`. -/
noncomputable def localVarianceRightFamily (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun uv =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
    { name := s!"localVariance.right({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- The same weighted operator on the first independently sampled point. -/
noncomputable def globalVarianceLeftFamily (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun uv =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
    { name := s!"globalVariance.left({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- The same weighted operator on the second independently sampled point. -/
noncomputable def globalVarianceRightFamily (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (PointPairQuestion params) Unit :=
  fun uv =>
    let op :=
      averageOperatorOverDistribution (polynomialDistribution params)
        (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
    { name := s!"globalVariance.right({params.m},{params.q},{params.d})"
      outcomeOperator := fun _ => op
      totalOperator := op }

/-- The edgewise squared norm expression in `lem:local-variance-of-points`. -/
noncomputable def localVarianceDeviationAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params))
    (g : Polynomial params) : Error :=
  placeholderAverageOverDistribution (rerandomizeCoord params)
    (fun uv =>
      operatorExpectation strategy.state
        (formalSquare
          (formalDifference
            (weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
            (weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2))))

/-- The independently sampled squared norm expression in `lem:global-variance-of-points`. -/
noncomputable def globalVarianceDeviationAtPolynomial (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params))
    (g : Polynomial params) : Error :=
  placeholderAverageOverDistribution (independentPointPair params)
    (fun uv =>
      operatorExpectation strategy.state
        (formalSquare
          (formalDifference
            (weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
            (weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2))))

/-- The polynomial-averaged local squared norm expression. -/
noncomputable def localVarianceDeviation (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) : Error :=
  averageOverDistribution (polynomialDistribution params)
    (fun g => localVarianceDeviationAtPolynomial params strategy G g)

/-- The polynomial-averaged global squared norm expression. -/
noncomputable def globalVarianceDeviation (params : Parameters)
    (strategy : SymmetricStrategy params)
    (G : SubMeasurement (Polynomial params)) : Error :=
  averageOverDistribution (polynomialDistribution params)
    (fun g => globalVarianceDeviationAtPolynomial params strategy G g)

/-- The displayed error term in `lem:generalize-b`. -/
noncomputable def generalizeBError (params : Parameters) : Error :=
  ((params.m : Error) * (params.d : Error)) / (params.q : Error)

/-- The displayed error term in `lem:local-variance-of-points`. -/
noncomputable def localVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (eps + delta + generalizeBError params)

/-- The displayed error term in `lem:global-variance-of-points`. -/
noncomputable def globalVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (params.m : Error) * (eps + delta + generalizeBError params)

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

/-- A concrete finite-dimensional realization of the Section 8 weighted operators. -/
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

/-- The concrete matrix-level counterpart of `lem:generalize-b`. -/
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

end MIPStarRE.Paper2009LDT.Section8GlobalVariance
