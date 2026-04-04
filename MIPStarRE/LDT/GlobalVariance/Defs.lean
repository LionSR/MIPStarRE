import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems

/-!
# Section 8 — Definitions

Definitions for the global variance analysis: axis-parallel line questions,
point-pair questions, polynomial families, and variance transfer constructions.
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

/-- Axis-parallel lines are finitely enumerable via their base point and direction. -/
noncomputable instance (params : Parameters) : Fintype (AxisParallelLine params) := by
  classical
  let e : AxisParallelLine params ≃ Point params × Fin params.m :=
    { toFun := fun ℓ => (ℓ.base, ℓ.direction)
      invFun := fun bd => { base := bd.1, direction := bd.2 }
      left_inv := by
        intro ℓ
        cases ℓ
        rfl
      right_inv := by
        intro bd
        cases bd
        rfl }
  exact Fintype.ofEquiv (Point params × Fin params.m) e.symm

/-- The placeholder finite polynomial model uses classical equality on the bundled witness. -/
noncomputable instance (params : Parameters) : DecidableEq (Polynomial params) :=
  Classical.decEq _

/-- A default low-degree polynomial used so uniform placeholder distributions are inhabited. -/
instance (params : Parameters) : Nonempty (Polynomial params) := by
  refine ⟨⟨0, ?_⟩⟩
  intro i
  -- Sound because each individual degree of the zero polynomial is `0`.
  simp [MvPolynomial.degreeOf_zero]

/-- Uniformly average a family of bounded operators into a `Unit`-valued submeasurement. -/
private noncomputable def uniformAverageUnitSubMeas {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → MIPStarRE.Quantum.Op ι)
    (hpsd : ∀ a, 0 ≤ f a) (hle : ∀ a, f a ≤ 1) :
    SubMeas Unit ι :=
  { outcome := fun _ => averageOperatorOverDistribution (uniformDistribution α) f
    total := averageOperatorOverDistribution (uniformDistribution α) f
    outcome_pos := by
      intro _
      simp only [averageOperatorOverDistribution, uniformDistribution, one_div]
      apply Finset.sum_nonneg
      intro a ha
      exact smul_nonneg (by positivity) (hpsd a)
    sum_eq_total := by
      simp
    total_le_one := by
      have hsum :
          ∑ a : α, (1 / (Fintype.card α : Error)) • f a ≤
            ∑ a : α, (1 / (Fintype.card α : Error)) • (1 : MIPStarRE.Quantum.Op ι) := by
        apply Finset.sum_le_sum
        intro a ha
        exact smul_le_smul_of_nonneg_left (hle a) (by positivity)
      have hconst :
          (∑ a : α, (1 / (Fintype.card α : Error)) • (1 : MIPStarRE.Quantum.Op ι)) =
            (1 : MIPStarRE.Quantum.Op ι) := by
        have hcard : (Fintype.card α : Error) ≠ 0 := by positivity
        calc
          ∑ a : α, (1 / (Fintype.card α : Error)) • (1 : MIPStarRE.Quantum.Op ι)
              = ((∑ a : α, (1 / (Fintype.card α : Error))) : Error) •
                  (1 : MIPStarRE.Quantum.Op ι) := by
                    simpa using
                      (Finset.sum_smul (s := Finset.univ)
                        (f := fun _ : α => (1 / (Fintype.card α : Error)))
                        (x := (1 : MIPStarRE.Quantum.Op ι))).symm
          _ = ((Fintype.card α : Error) * (1 / (Fintype.card α : Error))) •
                (1 : MIPStarRE.Quantum.Op ι) := by
                  simp [Finset.sum_const, nsmul_eq_mul]
          _ = (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
                congr 1
                field_simp [hcard]
          _ = 1 := by simp
      simpa [averageOperatorOverDistribution, uniformDistribution] using
        le_trans hsum (le_of_eq hconst) }

/-- The distribution of an axis-parallel line together with a point queried on it.

**Provisional placeholder**: uses the uniform distribution over all `(ℓ, u)` pairs,
including pairs where `u` is not on `ℓ`. The paper samples `ℓ` uniformly and then
`u` uniformly from `ℓ`. Replace with the correct conditional distribution once the
line-point sampling infrastructure is available. -/
noncomputable def axisParallelLineQuestionDistribution (params : Parameters) :
    Distribution (AxisParallelLineQuestion params) :=
  uniformDistribution (AxisParallelLineQuestion params) -- PROVISIONAL: see docstring

/-- A placeholder distribution over low-degree polynomials. -/
noncomputable def polynomialDistribution (params : Parameters) :
    Distribution (Polynomial params) :=
  uniformDistribution (Polynomial params)

/-- The operator `(G_g)^{1/2}` used throughout `expansion.tex`.
Uses `CFC.sqrt` (continuous functional calculus) to compute the matrix
square root of the PSD operator `G.outcome g`. -/
noncomputable def polynomialWeightSqrtOperator (params : Parameters)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  CFC.sqrt (G.outcome g)

/-- The weighted state `|ψ_g⟩ = (I ⊗ √G_g)|ψ⟩`, modeled as a density-matrix
transformation: `ρ_g = W_g ρ W_g†` where `W_g = I ⊗ √(G_g)`.

This is not necessarily normalized — normalization would require dividing by
`Tr(G_g ρ_B)`. We keep it unnormalized since the variance quantities in the
paper use unnormalized weighted expectations. -/
noncomputable def weightedPolynomialState (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    QuantumState (ι × ι) :=
  let sqrtG := polynomialWeightSqrtOperator params G g
  let W := rightTensor (ι₁ := ι) sqrtG
  { density := W * strategy.state.density * Wᴴ
    density_psd :=
      ((Matrix.nonneg_iff_posSemidef.mp strategy.state.density_psd).mul_mul_conjTranspose_same
        W).nonneg }

/-- The concrete operator `A^u_{g(u)}` for a fixed polynomial `g`. -/
def pointConditionedOutcomeOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op ι :=
  (strategy.pointMeasurement u).toSubMeas.outcome (g u)

/-- The paper's weighted operator `A^u_{g(u)} ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def weightedPointConditionedOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
    (polynomialWeightSqrtOperator params G g)

/-- The local variance of `A(g)` on the weighted state `|ψ_g⟩`.
Operators are lifted to the left tensor factor of the bipartite state. -/
noncomputable def pointConditionedLocalVarianceAtPolynomial (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  localVariance params
    (fun u => leftTensor (ι₂ := ι)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
    (weightedPolynomialState params strategy G g)

/-- The global variance of `A(g)` on the weighted state `|ψ_g⟩`.
Operators are lifted to the left tensor factor of the bipartite state. -/
noncomputable def pointConditionedGlobalVarianceAtPolynomial (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  globalVariance params
    (fun u => leftTensor (ι₂ := ι)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
    (weightedPolynomialState params strategy G g)

/-- The polynomial-averaged local variance of the conditioned points family. -/
noncomputable def pointConditionedLocalVariance (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)

/-- The polynomial-averaged global variance of the conditioned points family. -/
noncomputable def pointConditionedGlobalVariance (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)

/-- The event operator `B^ℓ_{[f(u)=g(u)]}`: sum of axis-line measurement
outcomes `f` that evaluate to the same value as `g` at point `u`. -/
noncomputable def generalizeBLeftOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  let (ℓ, u) := qu
  (postprocess
      ((strategy.axisParallelMeasurement ℓ).toSubMeas)
      (fun f : AxisLinePolynomial params =>
        if f.poly.eval (decodeScalar (u ℓ.direction)) = decodeScalar (g u) then
          some ()
        else
          none)).outcome (some ())

/-- The event operator `B^ℓ_{[f = g|_ℓ]}`: sum of axis-line measurement
outcomes `f` that agree with `g` restricted to line `ℓ`. -/
noncomputable def generalizeBRightOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  let ℓ := qu.1
  let gRestricted := Polynomial.restrictToAxisParallelLine params g ℓ
  (postprocess
      ((strategy.axisParallelMeasurement ℓ).toSubMeas)
      (fun f : AxisLinePolynomial params =>
        if f.poly = gRestricted.poly then
          some ()
        else
          none)).outcome (some ())

/-- The weighted left operator in `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def weightedGeneralizeBLeftOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (generalizeBLeftOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

/-- The weighted right operator in `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def weightedGeneralizeBRightOperatorAtPolynomial (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (generalizeBRightOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

-- TODO: blocked on CFC.sqrt monotonicity (CFC.sqrt G ≤ 1 when G ≤ 1)
private theorem pointConditionedOutcomeOperatorAtPolynomial_pos (params : Parameters)
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) :
    0 ≤ pointConditionedOutcomeOperatorAtPolynomial params strategy g u := by
  simpa [pointConditionedOutcomeOperatorAtPolynomial] using
    (strategy.pointMeasurement u).outcome_pos (g u)

-- TODO: blocked on CFC.sqrt monotonicity (CFC.sqrt G ≤ 1 when G ≤ 1)
private theorem pointConditionedOutcomeOperatorAtPolynomial_le_one (params : Parameters)
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) :
    pointConditionedOutcomeOperatorAtPolynomial params strategy g u ≤ 1 := by
  simpa [pointConditionedOutcomeOperatorAtPolynomial] using
    Measurement.outcome_le_one (strategy.pointMeasurement u).toMeasurement (g u)

-- TODO: blocked on CFC.sqrt monotonicity (CFC.sqrt G ≤ 1 when G ≤ 1)
private theorem generalizeBLeftOperatorAtPolynomial_pos (params : Parameters)
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    0 ≤ generalizeBLeftOperatorAtPolynomial params strategy g qu := by
  classical
  rcases qu with ⟨ℓ, u⟩
  simpa [generalizeBLeftOperatorAtPolynomial] using
    (postprocess
      ((strategy.axisParallelMeasurement ℓ).toSubMeas)
      (fun f : AxisLinePolynomial params =>
        if f.poly.eval (decodeScalar (u ℓ.direction)) = decodeScalar (g u) then
          some ()
        else
          none)).outcome_pos (some ())

-- TODO: blocked on CFC.sqrt monotonicity (CFC.sqrt G ≤ 1 when G ≤ 1)
private theorem generalizeBLeftOperatorAtPolynomial_le_one (params : Parameters)
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    generalizeBLeftOperatorAtPolynomial params strategy g qu ≤ 1 := by
  classical
  rcases qu with ⟨ℓ, u⟩
  simpa [generalizeBLeftOperatorAtPolynomial] using
    SubMeas.outcome_le_one
      (postprocess
        ((strategy.axisParallelMeasurement ℓ).toSubMeas)
        (fun f : AxisLinePolynomial params =>
          if f.poly.eval (decodeScalar (u ℓ.direction)) = decodeScalar (g u) then
            some ()
          else
            none))
      (some ())

-- TODO: blocked on CFC.sqrt monotonicity (CFC.sqrt G ≤ 1 when G ≤ 1)
private theorem generalizeBRightOperatorAtPolynomial_pos (params : Parameters)
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    0 ≤ generalizeBRightOperatorAtPolynomial params strategy g qu := by
  classical
  rcases qu with ⟨ℓ, u⟩
  simpa [generalizeBRightOperatorAtPolynomial] using
    (postprocess
      ((strategy.axisParallelMeasurement ℓ).toSubMeas)
      (fun f : AxisLinePolynomial params =>
        if f.poly = (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
          some ()
        else
          none)).outcome_pos (some ())

-- TODO: blocked on CFC.sqrt monotonicity (CFC.sqrt G ≤ 1 when G ≤ 1)
private theorem generalizeBRightOperatorAtPolynomial_le_one (params : Parameters)
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    generalizeBRightOperatorAtPolynomial params strategy g qu ≤ 1 := by
  classical
  rcases qu with ⟨ℓ, u⟩
  simpa [generalizeBRightOperatorAtPolynomial] using
    SubMeas.outcome_le_one
      (postprocess
        ((strategy.axisParallelMeasurement ℓ).toSubMeas)
        (fun f : AxisLinePolynomial params =>
          if f.poly = (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
            some ()
          else
            none))
      (some ())

-- TODO: blocked on CFC.sqrt monotonicity (CFC.sqrt G ≤ 1 when G ≤ 1)
private theorem weightedPointConditionedOperatorAtPolynomial_pos (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) :
    0 ≤ weightedPointConditionedOperatorAtPolynomial params strategy G g u := by
  exact opTensor_nonneg
    (pointConditionedOutcomeOperatorAtPolynomial_pos params strategy g u)
    (CFC.sqrt_nonneg (G.outcome g))

/-- `CFC.sqrt (G.outcome g) ≤ 1` when `G` is a submeasurement.
Follows from `(CFC.sqrt G)² = G ≤ 1` and `CFC.sqrt G ≥ 0`.
TODO: close the inner sorry via spectral decomposition. -/
private lemma cfc_sqrt_outcome_le_one (params : Parameters)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    CFC.sqrt (G.outcome g) ≤ 1 := by
  suffices h : CFC.sqrt (G.outcome g) * CFC.sqrt (G.outcome g) ≤ 1 by
    -- 0 ≤ P and P² ≤ 1 implies P ≤ 1 for Hermitian PSD matrices
    sorry
  rw [show CFC.sqrt (G.outcome g) * CFC.sqrt (G.outcome g) = G.outcome g from
    CFC.sqrt_mul_sqrt_self (G.outcome g) (G.outcome_pos g)]
  exact G.outcome_le_one g

private theorem weightedPointConditionedOperatorAtPolynomial_le_one (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) :
    weightedPointConditionedOperatorAtPolynomial params strategy G g u ≤ 1 := by
  calc weightedPointConditionedOperatorAtPolynomial params strategy G g u
      ≤ leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy g u) :=
        opTensor_le_leftTensor
          (pointConditionedOutcomeOperatorAtPolynomial_pos params strategy g u)
          (cfc_sqrt_outcome_le_one params G g)
    _ ≤ 1 := leftTensor_le_one
          (pointConditionedOutcomeOperatorAtPolynomial_le_one params strategy g u)

-- TODO: blocked on CFC.sqrt monotonicity (CFC.sqrt G ≤ 1 when G ≤ 1)
private theorem weightedGeneralizeBLeftOperatorAtPolynomial_pos (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    0 ≤ weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu := by
  exact opTensor_nonneg
    (generalizeBLeftOperatorAtPolynomial_pos params strategy g qu)
    (CFC.sqrt_nonneg (G.outcome g))

private theorem weightedGeneralizeBLeftOperatorAtPolynomial_le_one (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu ≤ 1 := by
  calc weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
      ≤ leftTensor (ι₂ := ι)
          (generalizeBLeftOperatorAtPolynomial params strategy g qu) :=
        opTensor_le_leftTensor
          (generalizeBLeftOperatorAtPolynomial_pos params strategy g qu)
          (cfc_sqrt_outcome_le_one params G g)
    _ ≤ 1 := leftTensor_le_one
          (generalizeBLeftOperatorAtPolynomial_le_one params strategy g qu)

-- TODO: blocked on CFC.sqrt monotonicity (CFC.sqrt G ≤ 1 when G ≤ 1)
private theorem weightedGeneralizeBRightOperatorAtPolynomial_pos (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    0 ≤ weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu := by
  exact opTensor_nonneg
    (generalizeBRightOperatorAtPolynomial_pos params strategy g qu)
    (CFC.sqrt_nonneg (G.outcome g))

private theorem weightedGeneralizeBRightOperatorAtPolynomial_le_one (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu ≤ 1 := by
  calc weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
      ≤ leftTensor (ι₂ := ι)
          (generalizeBRightOperatorAtPolynomial params strategy g qu) :=
        opTensor_le_leftTensor
          (generalizeBRightOperatorAtPolynomial_pos params strategy g qu)
          (cfc_sqrt_outcome_le_one params G g)
    _ ≤ 1 := leftTensor_le_one
          (generalizeBRightOperatorAtPolynomial_le_one params strategy g qu)

/-- The squared norm expression controlled by `lem:generalize-b` for a fixed `g`.
Uses bipartite state `ψbi` on `d * d`. -/
noncomputable def generalizeBDeviationAtPolynomial (params : Parameters)
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
noncomputable def generalizeBDeviation (params : Parameters)
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => generalizeBDeviationAtPolynomial params strategy ψbi G g)

/-- Aggregated family for the left-hand side of `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def generalizeBLeftFamily (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit (ι × ι) :=
  fun qu =>
    uniformAverageUnitSubMeas (α := Polynomial params)
      (fun g => weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
      (fun g => weightedGeneralizeBLeftOperatorAtPolynomial_pos params strategy G g qu)
      (fun g => weightedGeneralizeBLeftOperatorAtPolynomial_le_one params strategy G g qu)

/-- Aggregated family for the right-hand side of `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def generalizeBRightFamily (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit (ι × ι) :=
  fun qu =>
    uniformAverageUnitSubMeas (α := Polynomial params)
      (fun g => weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu)
      (fun g => weightedGeneralizeBRightOperatorAtPolynomial_pos params strategy G g qu)
      (fun g => weightedGeneralizeBRightOperatorAtPolynomial_le_one params strategy G g qu)

/-- Aggregated family for `A^u_[g(u)] ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def localVarianceLeftFamily (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  fun uv =>
    uniformAverageUnitSubMeas (α := Polynomial params)
      (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1)
      (fun g => weightedPointConditionedOperatorAtPolynomial_pos params strategy G g uv.1)
      (fun g => weightedPointConditionedOperatorAtPolynomial_le_one params strategy G g uv.1)

/-- Aggregated family for `A^v_[g(v)] ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def localVarianceRightFamily (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  fun uv =>
    uniformAverageUnitSubMeas (α := Polynomial params)
      (fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)
      (fun g => weightedPointConditionedOperatorAtPolynomial_pos params strategy G g uv.2)
      (fun g => weightedPointConditionedOperatorAtPolynomial_le_one params strategy G g uv.2)

/-- The same weighted operator on the first independently sampled point.
On the bipartite space `d * d`. -/
noncomputable def globalVarianceLeftFamily (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  localVarianceLeftFamily params strategy G

/-- The same weighted operator on the second independently sampled point.
On the bipartite space `d * d`. -/
noncomputable def globalVarianceRightFamily (params : Parameters)
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  localVarianceRightFamily params strategy G

/-- The edgewise squared norm expression in `lem:local-variance-of-points`.
Uses bipartite state `ψbi` on `d * d`. -/
noncomputable def localVarianceDeviationAtPolynomial (params : Parameters)
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
noncomputable def globalVarianceDeviationAtPolynomial (params : Parameters)
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
noncomputable def localVarianceDeviation (params : Parameters)
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => localVarianceDeviationAtPolynomial params strategy ψbi G g)

/-- The polynomial-averaged global squared norm expression. -/
noncomputable def globalVarianceDeviation (params : Parameters)
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => globalVarianceDeviationAtPolynomial params strategy ψbi G g)

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


end MIPStarRE.LDT.GlobalVariance
