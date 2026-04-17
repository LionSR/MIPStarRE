import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems

/-!
# Section 8 — Definitions

This file introduces the question types, weighted operators, aggregate families,
and error terms used in the global-variance part of the LDT development.

## References

- `blueprint/src/chapter/ch06_variance.tex`
- `references/ldt-paper/expansion.tex`
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]

/-! ## Basic question and answer types -/

/-- An axis-parallel line together with a point queried on that line. -/
abbrev AxisParallelLineQuestion (params : Parameters) :=
  AxisParallelLine params × Point params

/-- A pair of points used for local or global variance comparisons. -/
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
noncomputable instance (params : Parameters) [FieldModel params.q] :
    DecidableEq (Polynomial params) :=
  Classical.decEq _

/-- A default low-degree polynomial used so uniform placeholder distributions are inhabited. -/
instance (params : Parameters) [FieldModel params.q] : Nonempty (Polynomial params) := by
  exact ⟨⟨0, by
    intro i
    -- Sound because each individual degree of the zero polynomial is `0`.
    simp [MvPolynomial.degreeOf_zero]⟩⟩

/-! ## Uniform averages -/

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

/-- Public wrapper for the uniform `Unit`-valued average used by the aggregate
families in the global-variance lemmas. -/
noncomputable def averageUnitSubMeas {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → MIPStarRE.Quantum.Op ι)
    (hpsd : ∀ a, 0 ≤ f a) (hle : ∀ a, f a ≤ 1) :
    SubMeas Unit ι :=
  uniformAverageUnitSubMeas (ι := ι) f hpsd hle

/-- The unique outcome of `averageUnitSubMeas` is the uniform operator average
of the underlying family. -/
@[simp] lemma averageUnitSubMeas_outcome
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (f : α → MIPStarRE.Quantum.Op ι)
    (hpsd : ∀ a, 0 ≤ f a) (hle : ∀ a, f a ≤ 1) :
    (averageUnitSubMeas (ι := ι) f hpsd hle).outcome () =
      averageOperatorOverDistribution (uniformDistribution α) f :=
  rfl

/-- A valid axis-parallel line question pairs a line with a point lying on it. -/
def pointOnLine {params : Parameters} [FieldModel params.q]
    (qu : AxisParallelLineQuestion params) : Prop :=
  ∃ t : Fq params, qu.1.pointAt t = qu.2

/-- The affine line parameter of the sampled point in an axis-parallel line question.

For a line `ℓ(t) = base + t e_i`, the sampled point `u` has affine parameter
`u_i - base_i`. This is the parameter used by the axis-parallel line-test API;
it is not the raw coordinate `u_i` unless the line base has zero in direction `i`. -/
def axisParallelLineQuestionParameter {params : Parameters} [FieldModel params.q]
    (qu : AxisParallelLineQuestion params) : Fq params :=
  subCoord (qu.2 qu.1.direction) (qu.1.base qu.1.direction)

/-- The recovered parameter of `ℓ.pointAt t` is exactly `t`. -/
@[simp] theorem axisParallelLineQuestionParameter_pointAt {params : Parameters}
    [FieldModel params.q] (ℓ : AxisParallelLine params) (t : Fq params) :
    axisParallelLineQuestionParameter (ℓ, ℓ.pointAt t) = t := by
  simp only [axisParallelLineQuestionParameter, AxisParallelLine.pointAt, if_pos]
  simp [subCoord, addCoord]

/-- The distribution of an axis-parallel line together with a point queried on it.

The paper samples `u ∈ F_q^m` uniformly, then samples a direction `i` uniformly,
and finally takes the axis-parallel line through `u` in direction `i`. Since
`AxisParallelLineQuestion params` is represented as a pair `(ℓ, u)`, we realize
this as the normalized uniform distribution on the finite set of incident pairs,
i.e. those with `u ∈ ℓ`. -/
noncomputable def axisParallelLineQuestionDistribution (params : Parameters) [FieldModel params.q] :
    Distribution (AxisParallelLineQuestion params) := by
  classical
  let support : Finset (AxisParallelLineQuestion params) :=
    Finset.univ.filter (pointOnLine (params := params))
  exact
    { support := support
      weight := fun qu => if qu ∈ support then 1 / (support.card : Error) else 0
      nonnegative := by
        intro qu
        by_cases hqu : qu ∈ support <;> simp [hqu]
      outsideSupport := by
        intro qu hqu
        simp [hqu] }

/-- A placeholder distribution over low-degree polynomials. -/
noncomputable def polynomialDistribution (params : Parameters) [FieldModel params.q] :
    Distribution (Polynomial params) :=
  uniformDistribution (Polynomial params)

/-! ## Weighted operators and variance families -/

/-- The operator `(G_g)^{1/2}` used throughout `expansion.tex`.
Uses `CFC.sqrt` (continuous functional calculus) to compute the matrix
square root of the PSD operator `G.outcome g`. -/
noncomputable def polynomialWeightSqrtOperator (params : Parameters) [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  CFC.sqrt (G.outcome g)

/-- The weighted state `|ψ_g⟩ = (I ⊗ √G_g)|ψ⟩`, modeled as a density-matrix
transformation: `ρ_g = W_g ρ W_g†` where `W_g = I ⊗ √(G_g)`.

This is not necessarily normalized — normalization would require dividing by
`Tr(G_g ρ_B)`. We keep it unnormalized since the variance quantities in the
paper use unnormalized weighted expectations. -/
noncomputable def weightedPolynomialState (params : Parameters) [FieldModel params.q]
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
def pointConditionedOutcomeOperatorAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op ι :=
  (strategy.pointMeasurement u).toSubMeas.outcome (g u)

/-- The paper's weighted operator `A^u_{g(u)} ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def weightedPointConditionedOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
    (polynomialWeightSqrtOperator params G g)

/-- The local variance of `A(g)` on the weighted state `|ψ_g⟩`.
Operators are lifted to the left tensor factor of the bipartite state. -/
noncomputable def pointConditionedLocalVarianceAtPolynomial (params : Parameters)
    [FieldModel params.q]
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
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  globalVariance params
    (fun u => leftTensor (ι₂ := ι)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
    (weightedPolynomialState params strategy G g)

/-- The polynomial-averaged local variance of the conditioned points family. -/
noncomputable def pointConditionedLocalVariance (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)

/-- The polynomial-averaged global variance of the conditioned points family. -/
noncomputable def pointConditionedGlobalVariance (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)

private noncomputable def generalizeBLeftEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) ι :=
  let (ℓ, u) := qu
  postprocess
    ((strategy.axisParallelMeasurement ℓ).toSubMeas)
    (fun f : AxisLinePolynomial params =>
      if f (axisParallelLineQuestionParameter qu) = g u then
        some ()
      else
        none)

private noncomputable def generalizeBRightEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) ι :=
  let ℓ := qu.1
  let gRestricted := Polynomial.restrictToAxisParallelLine params g ℓ
  postprocess
    ((strategy.axisParallelMeasurement ℓ).toSubMeas)
    (fun f : AxisLinePolynomial params =>
      if f.poly = gRestricted.poly then
        some ()
      else
        none)

/-- The event operator `B^ℓ_{[f(u)=g(u)]}`: sum of axis-line measurement
outcomes `f` that evaluate to the same value as `g` at point `u`. -/
noncomputable def generalizeBLeftOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  (generalizeBLeftEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The event operator `B^ℓ_{[f = g|_ℓ]}`: sum of axis-line measurement
outcomes `f` that agree with `g` restricted to line `ℓ`. -/
noncomputable def generalizeBRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  (generalizeBRightEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The weighted left operator in `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def weightedGeneralizeBLeftOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
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
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (generalizeBRightOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

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

/-- The displayed error term in `lem:local-variance-of-points`. -/
noncomputable def localVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (eps + delta + generalizeBError params)

/-- The displayed error term in `lem:global-variance-of-points`. -/
noncomputable def globalVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (params.m : Error) * (eps + delta + generalizeBError params)


end MIPStarRE.LDT.GlobalVariance
