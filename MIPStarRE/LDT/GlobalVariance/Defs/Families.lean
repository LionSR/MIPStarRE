import MIPStarRE.LDT.GlobalVariance.Defs.Operators

/-!
# Section 8 global variance: operator families

Positivity and normalization lemmas for the point-conditioned outcome
operator families used to build the global-variance comparisons.

## References

- arXiv:2009.12982, Section 8 (global variance).
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]

private theorem pointConditionedOutcomeOperatorAtPolynomial_pos (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) :
    0 ≤ pointConditionedOutcomeOperatorAtPolynomial params strategy g u := by
  simpa [pointConditionedOutcomeOperatorAtPolynomial] using
    (strategy.pointMeasurement u).outcome_pos (g u)

private theorem pointConditionedOutcomeOperatorAtPolynomial_le_one (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) :
    pointConditionedOutcomeOperatorAtPolynomial params strategy g u ≤ 1 := by
  simpa [pointConditionedOutcomeOperatorAtPolynomial] using
    Measurement.outcome_le_one (strategy.pointMeasurement u).toMeasurement (g u)

private theorem generalizeBLeftOperatorAtPolynomial_pos (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    0 ≤ generalizeBLeftOperatorAtPolynomial params strategy g qu := by
  simpa [generalizeBLeftOperatorAtPolynomial] using
    (generalizeBLeftEventSubMeasAtPolynomial params strategy g qu).outcome_pos (some ())

private theorem generalizeBLeftOperatorAtPolynomial_le_one (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    generalizeBLeftOperatorAtPolynomial params strategy g qu ≤ 1 := by
  simpa [generalizeBLeftOperatorAtPolynomial] using
    SubMeas.outcome_le_one
      (generalizeBLeftEventSubMeasAtPolynomial params strategy g qu)
      (some ())

private theorem generalizeBRightOperatorAtPolynomial_pos (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    0 ≤ generalizeBRightOperatorAtPolynomial params strategy g qu := by
  simpa [generalizeBRightOperatorAtPolynomial] using
    (generalizeBRightEventSubMeasAtPolynomial params strategy g qu).outcome_pos (some ())

private theorem generalizeBRightOperatorAtPolynomial_le_one (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    generalizeBRightOperatorAtPolynomial params strategy g qu ≤ 1 := by
  simpa [generalizeBRightOperatorAtPolynomial] using
    SubMeas.outcome_le_one
      (generalizeBRightEventSubMeasAtPolynomial params strategy g qu)
      (some ())

/-- `CFC.sqrt (G.outcome g) ≤ 1` when `G` is a submeasurement.
Proved via the NNReal CFC spectrum API: `G.outcome g ≤ 1` means all
spectral values satisfy `λ ≤ 1`, so `√λ ≤ 1` as well. -/
private lemma cfc_sqrt_outcome_le_one (params : Parameters) [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    CFC.sqrt (G.outcome g) ≤ 1 := by
  have hspec_le : ∀ x, x ∈ spectrum NNReal (G.outcome g) → x ≤ 1 := by
    have hle : G.outcome g ≤ 1 := G.outcome_le_one g
    rw [← cfc_id' NNReal (G.outcome g) (ha := G.outcome_pos g),
      ← cfc_const_one (R := NNReal) (G.outcome g) (ha := G.outcome_pos g),
      cfc_nnreal_le_iff _ _ _ (SpectrumRestricts.nnreal_of_nonneg (G.outcome_pos g))
        (ha := G.outcome_pos g)] at hle
    exact hle
  rw [CFC.sqrt_eq_cfc, ← cfc_const_one (R := NNReal) (G.outcome g) (ha := G.outcome_pos g),
    cfc_nnreal_le_iff _ _ _ (SpectrumRestricts.nnreal_of_nonneg (G.outcome_pos g))
      (ha := G.outcome_pos g)]
  intro x hx
  -- √x ≤ 1 follows from x ≤ 1 for NNReal (NNReal.sqrt_le_one)
  simpa using hspec_le x hx

private theorem weightedPolynomialOperator_pos (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    {A : MIPStarRE.Quantum.Op ι} (hA : 0 ≤ A) :
    0 ≤ opTensor A (polynomialWeightSqrtOperator params G g) := by
  simpa [polynomialWeightSqrtOperator] using
    (opTensor_nonneg hA (CFC.sqrt_nonneg (G.outcome g)))

private theorem weightedPolynomialOperator_le_one (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    {A : MIPStarRE.Quantum.Op ι}
    (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1) :
    opTensor A (polynomialWeightSqrtOperator params G g) ≤ 1 := by
  calc
    opTensor A (polynomialWeightSqrtOperator params G g)
      ≤ leftTensor (ι₂ := ι) A :=
        opTensor_le_leftTensor hA_pos (cfc_sqrt_outcome_le_one params G g)
    _ ≤ 1 := leftTensor_le_one hA_le_one

private theorem weightedPointConditionedOperatorAtPolynomial_pos (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) :
    0 ≤ weightedPointConditionedOperatorAtPolynomial params strategy G g u := by
  simpa [weightedPointConditionedOperatorAtPolynomial] using
    (weightedPolynomialOperator_pos (ι := ι) (params := params) (G := G) (g := g)
      (A := pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
      (pointConditionedOutcomeOperatorAtPolynomial_pos params strategy g u))

private theorem weightedPointConditionedOperatorAtPolynomial_le_one (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) :
    weightedPointConditionedOperatorAtPolynomial params strategy G g u ≤ 1 := by
  simpa [weightedPointConditionedOperatorAtPolynomial] using
    (weightedPolynomialOperator_le_one (ι := ι) (params := params) (G := G) (g := g)
      (A := pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
      (pointConditionedOutcomeOperatorAtPolynomial_pos params strategy g u)
      (pointConditionedOutcomeOperatorAtPolynomial_le_one params strategy g u))

private theorem weightedGeneralizeBLeftOperatorAtPolynomial_pos (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    0 ≤ weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu := by
  simpa [weightedGeneralizeBLeftOperatorAtPolynomial] using
    (weightedPolynomialOperator_pos (ι := ι) (params := params) (G := G) (g := g)
      (A := generalizeBLeftOperatorAtPolynomial params strategy g qu)
      (generalizeBLeftOperatorAtPolynomial_pos params strategy g qu))

private theorem weightedGeneralizeBLeftOperatorAtPolynomial_le_one (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu ≤ 1 := by
  simpa [weightedGeneralizeBLeftOperatorAtPolynomial] using
    (weightedPolynomialOperator_le_one (ι := ι) (params := params) (G := G) (g := g)
      (A := generalizeBLeftOperatorAtPolynomial params strategy g qu)
      (generalizeBLeftOperatorAtPolynomial_pos params strategy g qu)
      (generalizeBLeftOperatorAtPolynomial_le_one params strategy g qu))

private theorem weightedGeneralizeBRightOperatorAtPolynomial_pos (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    0 ≤ weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu := by
  simpa [weightedGeneralizeBRightOperatorAtPolynomial] using
    (weightedPolynomialOperator_pos (ι := ι) (params := params) (G := G) (g := g)
      (A := generalizeBRightOperatorAtPolynomial params strategy g qu)
      (generalizeBRightOperatorAtPolynomial_pos params strategy g qu))

private theorem weightedGeneralizeBRightOperatorAtPolynomial_le_one (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu ≤ 1 := by
  simpa [weightedGeneralizeBRightOperatorAtPolynomial] using
    (weightedPolynomialOperator_le_one (ι := ι) (params := params) (G := G) (g := g)
      (A := generalizeBRightOperatorAtPolynomial params strategy g qu)
      (generalizeBRightOperatorAtPolynomial_pos params strategy g qu)
      (generalizeBRightOperatorAtPolynomial_le_one params strategy g qu))

/-- The squared norm expression controlled by `lem:generalize-b` for a fixed `g`.
Uses bipartite state `ψbi` on `d * d`. -/
noncomputable def generalizeBDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (axisParallelLineQuestionDistribution params)
    (fun qu =>
      let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
               weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
      ev ψbi (Dᴴ * D))

/-- The polynomial-averaged deviation controlled by `lem:generalize-b`. -/
noncomputable def generalizeBDeviation (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => generalizeBDeviationAtPolynomial params strategy ψbi G g)

/-- The line-collision residual obtained after expanding the projective line
measurement in `lem:generalize-b` and moving the polynomial weight from
`(G_g)^{1/2}` to `G_g`.  The remaining unproved analytic step is to bound this
quantity by Schwartz--Zippel and the submeasurement property of `G`. -/
noncomputable def generalizeBCollisionResidual (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (axisParallelLineQuestionDistribution params)
    (fun qu =>
      ev ψbi (opTensor
        (generalizeBCollisionOperatorAtPolynomial params strategy g qu)
        (G.outcome g)))

/-- Explicit line/parameter expansion of the `lem:generalize-b` collision residual.

This is the paper's `expansion.tex`, lines 286--288, after replacing an
incident line question `(ℓ,u)` by a line `ℓ` and affine parameter `t` with
`u = ℓ(t)`: the coefficient is the fraction of parameters where a line answer
`f` both collides with `g|_ℓ` at `t` and is not equal to `g|_ℓ`.  Issue #753
reduces the remaining residual work to proving that
`generalizeBCollisionResidual` is equal to this explicit expansion. -/
noncomputable def generalizeBLineCollisionExpansion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (uniformDistribution (AxisParallelLine params))
    (fun ℓ =>
      ∑ f : AxisLinePolynomial params,
        avgOver (uniformDistribution (Fq params))
          (fun t =>
            if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
              (1 : Error)
            else 0) *
          ev ψbi (opTensor
            ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
            (G.outcome g)))

private noncomputable def polynomialAverageUnitSubMeas (params : Parameters)
    [FieldModel params.q]
    (f : Polynomial params → MIPStarRE.Quantum.Op (ι × ι))
    (hpos : ∀ g : Polynomial params, 0 ≤ f g)
    (hle : ∀ g : Polynomial params, f g ≤ 1) :
    SubMeas Unit (ι × ι) :=
  averageUnitSubMeas (α := Polynomial params) f hpos hle

/-- The unique outcome of the polynomial average helper is its uniform operator average. -/
@[simp] lemma polynomialAverageUnitSubMeas_outcome (params : Parameters)
    [FieldModel params.q]
    (f : Polynomial params → MIPStarRE.Quantum.Op (ι × ι))
    (hpos : ∀ g : Polynomial params, 0 ≤ f g)
    (hle : ∀ g : Polynomial params, f g ≤ 1) :
    (polynomialAverageUnitSubMeas (ι := ι) params f hpos hle).outcome () =
      averageOperatorOverDistribution (uniformDistribution (Polynomial params)) f :=
  rfl

/-- The total of the polynomial average helper is its uniform operator average. -/
@[simp] lemma polynomialAverageUnitSubMeas_total (params : Parameters)
    [FieldModel params.q]
    (f : Polynomial params → MIPStarRE.Quantum.Op (ι × ι))
    (hpos : ∀ g : Polynomial params, 0 ≤ f g)
    (hle : ∀ g : Polynomial params, f g ≤ 1) :
    (polynomialAverageUnitSubMeas (ι := ι) params f hpos hle).total =
      averageOperatorOverDistribution (uniformDistribution (Polynomial params)) f :=
  rfl

/-- Aggregated family for the left-hand side of `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def generalizeBLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit (ι × ι) :=
  fun qu =>
    polynomialAverageUnitSubMeas params
      (fun g => weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
      (fun g => weightedGeneralizeBLeftOperatorAtPolynomial_pos params strategy G g qu)
      (fun g => weightedGeneralizeBLeftOperatorAtPolynomial_le_one params strategy G g qu)

/-- Aggregated family for the right-hand side of `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def generalizeBRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit (ι × ι) :=
  fun qu =>
    polynomialAverageUnitSubMeas params
      (fun g => weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)
      (fun g => weightedGeneralizeBRightOperatorAtPolynomial_pos params strategy G g qu)
      (fun g => weightedGeneralizeBRightOperatorAtPolynomial_le_one params strategy G g qu)

/-- Aggregated family for `A^u_[g(u)] ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def localVarianceLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  fun uv =>
    polynomialAverageUnitSubMeas params
      (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
      (fun g => weightedPointConditionedOperatorAtPolynomial_pos params strategy G g uv.1)
      (fun g => weightedPointConditionedOperatorAtPolynomial_le_one params strategy G g uv.1)

/-- Aggregated family for `A^v_[g(v)] ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def localVarianceRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  fun uv =>
    polynomialAverageUnitSubMeas params
      (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
      (fun g => weightedPointConditionedOperatorAtPolynomial_pos params strategy G g uv.2)
      (fun g => weightedPointConditionedOperatorAtPolynomial_le_one params strategy G g uv.2)

/-- The same weighted operator on the first independently sampled point.
On the bipartite space `d * d`. -/
noncomputable def globalVarianceLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  localVarianceLeftFamily params strategy G

/-- The same weighted operator on the second independently sampled point.
On the bipartite space `d * d`. -/
noncomputable def globalVarianceRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  localVarianceRightFamily params strategy G

/-- The edgewise squared norm expression in `lem:local-variance-of-points`.
Uses bipartite state `ψbi` on `d * d`. -/
noncomputable def localVarianceDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (rerandomizeCoord params)
    (fun uv =>
      let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
               weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
      ev ψbi (Dᴴ * D))

/-- The independently sampled squared norm expression in `lem:global-variance-of-points`.
Uses bipartite state `ψbi` on `d * d`. -/
noncomputable def globalVarianceDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (independentPointPair params)
    (fun uv =>
      let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
               weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
      ev ψbi (Dᴴ * D))

/-- The polynomial-averaged local squared norm expression. -/
noncomputable def localVarianceDeviation (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => localVarianceDeviationAtPolynomial params strategy ψbi G g)

/-- The polynomial-averaged global squared norm expression. -/
noncomputable def globalVarianceDeviation (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => globalVarianceDeviationAtPolynomial params strategy ψbi G g)

/-- The displayed error term in `lem:generalize-b`. -/
noncomputable def generalizeBError (params : Parameters) : Error :=
  ((params.m : Error) * (params.d : Error)) / (params.q : Error)

/-- The sharp sum of the six displayed transport errors in
`lem:local-variance-of-points`, before the paper applies the multi-step
triangle inequality.

The six steps in `references/ldt-paper/expansion.tex`, lines 305--311 have
errors `2δ`, `2ε`, `md/q`, `md/q`, `2ε`, and `2δ`, so the chain contributes
`4ε + 4δ + 2md/q`. -/
noncomputable def localVarianceTransportChainError (params : Parameters)
    (eps delta : Error) : Error :=
  4 * eps + 4 * delta + 2 * generalizeBError params

/-- The displayed error term in `lem:local-variance-of-points`. -/
noncomputable def localVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (eps + delta + generalizeBError params)

/-- The displayed error term in `lem:global-variance-of-points`. -/
noncomputable def globalVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (params.m : Error) * (eps + delta + generalizeBError params)

end MIPStarRE.LDT.GlobalVariance
