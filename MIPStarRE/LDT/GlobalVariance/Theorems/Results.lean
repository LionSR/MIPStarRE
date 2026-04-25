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


/-! ## Algebraic norm/variance reductions -/

private lemma polynomialWeightSqrtOperator_conjTranspose
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    (polynomialWeightSqrtOperator params G g)ᴴ =
      polynomialWeightSqrtOperator params G g := by
  simpa [polynomialWeightSqrtOperator] using
    (CFC.sqrt_nonneg (G.outcome g)).isSelfAdjoint

private lemma polynomialWeightSqrtOperator_mul_self
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    polynomialWeightSqrtOperator params G g *
        polynomialWeightSqrtOperator params G g =
      G.outcome g := by
  simpa [polynomialWeightSqrtOperator] using
    CFC.sqrt_mul_sqrt_self (G.outcome g) (G.outcome_pos g)

private lemma leftTensor_sub
    {A B : MIPStarRE.Quantum.Op ι} :
    leftTensor (ι₂ := ι) A - leftTensor (ι₂ := ι) B =
      leftTensor (ι₂ := ι) (A - B) := by
  simpa [leftTensor] using
    (opTensor_sub_left (ι₁ := ι) (ι₂ := ι) A B (1 : MIPStarRE.Quantum.Op ι))

private lemma weightedPointConditionedOperator_sub
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params)
    (u v : Point params) :
    weightedPointConditionedOperatorAtPolynomial params strategy G g u -
        weightedPointConditionedOperatorAtPolynomial params strategy G g v =
      opTensor
        (pointConditionedOutcomeOperatorAtPolynomial params strategy g u -
          pointConditionedOutcomeOperatorAtPolynomial params strategy g v)
        (polynomialWeightSqrtOperator params G g) := by
  simp [weightedPointConditionedOperatorAtPolynomial, opTensor_sub_left]

private lemma weightedPointConditionedOperator_sq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params)
    (u v : Point params) :
    let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
        weightedPointConditionedOperatorAtPolynomial params strategy G g v
    Dᴴ * D =
      opTensor
        (((pointConditionedOutcomeOperatorAtPolynomial params strategy g u -
          pointConditionedOutcomeOperatorAtPolynomial params strategy g v)ᴴ) *
            (pointConditionedOutcomeOperatorAtPolynomial params strategy g u -
              pointConditionedOutcomeOperatorAtPolynomial params strategy g v))
        (G.outcome g) := by
  dsimp only
  rw [weightedPointConditionedOperator_sub]
  rw [conjTranspose_opTensor, opTensor_mul]
  rw [polynomialWeightSqrtOperator_conjTranspose,
    polynomialWeightSqrtOperator_mul_self]

/-- Move a left-register observable from the polynomial-weighted state
`(I ⊗ √G_g) ρ (I ⊗ √G_g)ᴴ` back to the original bipartite state. -/
private lemma weightedPolynomialState_ev_leftTensor
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params)
    (X : MIPStarRE.Quantum.Op ι) :
    ev (weightedPolynomialState params strategy G g) (leftTensor (ι₂ := ι) X) =
      ev strategy.state (opTensor X (G.outcome g)) := by
  let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
  let W : MIPStarRE.Quantum.Op (ι × ι) := rightTensor (ι₁ := ι) S
  let L : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) X
  have hS_self : Sᴴ = S := by
    simpa [S] using polynomialWeightSqrtOperator_conjTranspose (params := params) G g
  have hS_sq : S * S = G.outcome g := by
    simpa [S] using polynomialWeightSqrtOperator_mul_self (params := params) G g
  have htarget : Wᴴ * L * W = opTensor X (G.outcome g) := by
    calc
      Wᴴ * L * W =
          rightTensor (ι₁ := ι) Sᴴ * leftTensor (ι₂ := ι) X * rightTensor (ι₁ := ι) S := by
        simp [W, L, rightTensor, Matrix.conjTranspose_kronecker]
      _ = opTensor X Sᴴ * rightTensor (ι₁ := ι) S := by
        rw [rightTensor_mul_leftTensor_eq_opTensor]
      _ = (leftTensor (ι₂ := ι) X * rightTensor (ι₁ := ι) Sᴴ) *
          rightTensor (ι₁ := ι) S := by
        rw [leftTensor_mul_rightTensor_eq_opTensor]
      _ = leftTensor (ι₂ := ι) X *
          (rightTensor (ι₁ := ι) Sᴴ * rightTensor (ι₁ := ι) S) := by
        simp [mul_assoc]
      _ = leftTensor (ι₂ := ι) X * rightTensor (ι₁ := ι) (Sᴴ * S) := by
        rw [rightTensor_mul_rightTensor]
      _ = opTensor X (G.outcome g) := by
        rw [hS_self, hS_sq, leftTensor_mul_rightTensor_eq_opTensor]
  change
    Complex.re (MIPStarRE.Quantum.normalizedTrace ((W * strategy.state.density * Wᴴ) * L)) =
      Complex.re
        (MIPStarRE.Quantum.normalizedTrace
          (strategy.state.density * opTensor X (G.outcome g)))
  congr 1
  calc
    MIPStarRE.Quantum.normalizedTrace ((W * strategy.state.density * Wᴴ) * L)
      = MIPStarRE.Quantum.normalizedTrace (W * (strategy.state.density * Wᴴ * L)) := by
        simp [mul_assoc]
    _ = MIPStarRE.Quantum.normalizedTrace ((strategy.state.density * Wᴴ * L) * W) := by
        rw [MIPStarRE.Quantum.normalizedTrace_mul_comm]
    _ = MIPStarRE.Quantum.normalizedTrace (strategy.state.density * (Wᴴ * L * W)) := by
        simp [mul_assoc]
    _ = MIPStarRE.Quantum.normalizedTrace (strategy.state.density * opTensor X (G.outcome g)) := by
        rw [htarget]

private lemma pointConditioned_leftTensor_sq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) (g : Polynomial params)
    (u v : Point params) :
    let D := leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy g u) -
        leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy g v)
    Dᴴ * D =
      leftTensor (ι₂ := ι)
        (((pointConditionedOutcomeOperatorAtPolynomial params strategy g u -
          pointConditionedOutcomeOperatorAtPolynomial params strategy g v)ᴴ) *
            (pointConditionedOutcomeOperatorAtPolynomial params strategy g u -
              pointConditionedOutcomeOperatorAtPolynomial params strategy g v)) := by
  dsimp only
  rw [leftTensor_sub]
  have hct :
      (leftTensor (ι₂ := ι)
        (pointConditionedOutcomeOperatorAtPolynomial params strategy g u -
          pointConditionedOutcomeOperatorAtPolynomial params strategy g v))ᴴ =
        leftTensor (ι₂ := ι)
          ((pointConditionedOutcomeOperatorAtPolynomial params strategy g u -
            pointConditionedOutcomeOperatorAtPolynomial params strategy g v)ᴴ) := by
    simpa [leftTensor] using
      (conjTranspose_opTensor
        (pointConditionedOutcomeOperatorAtPolynomial params strategy g u -
          pointConditionedOutcomeOperatorAtPolynomial params strategy g v)
        (1 : MIPStarRE.Quantum.Op ι))
  rw [hct]
  rw [leftTensor_mul_leftTensor]

/-- The edgewise weighted squared-difference expression is exactly twice the
local variance of the point-conditioned family on the weighted state. This is
`eq:equivalent-local-variance` unpacked at a fixed polynomial. -/
lemma localVarianceDeviationAtPolynomial_eq_two_pointConditionedLocalVarianceAtPolynomial
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    localVarianceDeviationAtPolynomial params strategy strategy.state G g =
      2 * pointConditionedLocalVarianceAtPolynomial params strategy G g := by
  unfold localVarianceDeviationAtPolynomial pointConditionedLocalVarianceAtPolynomial localVariance
  rw [← mul_assoc]
  rw [show (2 : Error) * (1 / 2 : Error) = 1 by norm_num]
  rw [one_mul]
  apply avgOver_congr
  intro uv
  change
    ev strategy.state
        (((weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)ᴴ) *
          (weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)) =
      ev (weightedPolynomialState params strategy G g)
        (pointDifferenceSquaredOperator
          (fun u => leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)) uv.1 uv.2)
  rw [weightedPointConditionedOperator_sq]
  unfold pointDifferenceSquaredOperator
  rw [← weightedPolynomialState_ev_leftTensor]
  rw [pointConditioned_leftTensor_sq]

/-- The independent-points weighted squared-difference expression is exactly
twice the global variance of the point-conditioned family on the weighted state. -/
lemma globalVarianceDeviationAtPolynomial_eq_two_pointConditionedGlobalVarianceAtPolynomial
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    globalVarianceDeviationAtPolynomial params strategy strategy.state G g =
      2 * pointConditionedGlobalVarianceAtPolynomial params strategy G g := by
  unfold globalVarianceDeviationAtPolynomial pointConditionedGlobalVarianceAtPolynomial
    globalVariance
  rw [← mul_assoc]
  rw [show (2 : Error) * (1 / 2 : Error) = 1 by norm_num]
  rw [one_mul]
  apply avgOver_congr
  intro uv
  change
    ev strategy.state
        (((weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)ᴴ) *
          (weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2)) =
      ev (weightedPolynomialState params strategy G g)
        (pointDifferenceSquaredOperator
          (fun u => leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)) uv.1 uv.2)
  rw [weightedPointConditionedOperator_sq]
  unfold pointDifferenceSquaredOperator
  rw [← weightedPolynomialState_ev_leftTensor]
  rw [pointConditioned_leftTensor_sq]

private lemma pointConditionedLocalVarianceAtPolynomial_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    0 ≤ pointConditionedLocalVarianceAtPolynomial params strategy G g := by
  unfold pointConditionedLocalVarianceAtPolynomial localVariance
  exact mul_nonneg (by norm_num)
    (avgOver_nonneg (rerandomizeCoord params) _ fun uv =>
      ev_adjoint_self_nonneg (weightedPolynomialState params strategy G g)
        (leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy g uv.1) -
        leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy g uv.2)))

/-- A bound on the edgewise weighted norm expression implies the corresponding
bound on the local variance. The factor `1/2` in `localVariance` only strengthens
the estimate. -/
lemma pointConditionedLocalVarianceAtPolynomial_le_of_deviation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) {g : Polynomial params} {η : Error}
    (hdev : localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤ η) :
    pointConditionedLocalVarianceAtPolynomial params strategy G g ≤ η := by
  have heq :=
    localVarianceDeviationAtPolynomial_eq_two_pointConditionedLocalVarianceAtPolynomial
      params strategy G g
  have hnonneg := pointConditionedLocalVarianceAtPolynomial_nonneg params strategy G g
  calc
    pointConditionedLocalVarianceAtPolynomial params strategy G g
        ≤ localVarianceDeviationAtPolynomial params strategy strategy.state G g := by
          rw [heq]
          nlinarith
    _ ≤ η := hdev

/-- Pointwise local-to-global transfer for the paper's weighted squared-norm
form: the independent-points expression is at most `m` times the edge expression.
This combines `lem:local-to-global` with the two exact norm/variance identities
above, so no independent global-deviation hypothesis is needed. -/
lemma globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    globalVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
      (params.m : Error) *
        localVarianceDeviationAtPolynomial params strategy strategy.state G g := by
  have hglobal :=
    globalVarianceDeviationAtPolynomial_eq_two_pointConditionedGlobalVarianceAtPolynomial
      params strategy G g
  have hlocal :=
    localVarianceDeviationAtPolynomial_eq_two_pointConditionedLocalVarianceAtPolynomial
      params strategy G g
  calc
    globalVarianceDeviationAtPolynomial params strategy strategy.state G g
        = 2 * pointConditionedGlobalVarianceAtPolynomial params strategy G g := hglobal
    _ ≤ 2 * ((params.m : Error) *
          pointConditionedLocalVarianceAtPolynomial params strategy G g) := by
        exact mul_le_mul_of_nonneg_left
          (pointConditionedExpansionTransfer params strategy G g) (by norm_num)
    _ = (params.m : Error) *
          (2 * pointConditionedLocalVarianceAtPolynomial params strategy G g) := by
        ring
    _ = (params.m : Error) *
          localVarianceDeviationAtPolynomial params strategy strategy.state G g := by
        rw [hlocal]

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
  -- self-improvement pipeline it is supplied as an explicit theorem
  -- hypothesis.
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

/-- Legacy wrapper for `lem:local-variance-of-points` with arbitrary bipartite
state and both pointwise bounds supplied explicitly.

For the paper-faithful strategy state, prefer
`localVarianceOfPointsFromEdgeDeviation`, which derives the local-variance bound
from the edgewise weighted norm estimate. -/
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


/-! ## Strategy-state reductions -/

/-- Strict reduction for `lem:local-variance-of-points` on the strategy state.

Compared with the legacy wrapper `localVarianceOfPoints`, this theorem no longer
requires the local-variance bound as a separate hypothesis: it derives it from
the edgewise weighted squared-norm estimate using
`localVarianceDeviationAtPolynomial_eq_two_pointConditionedLocalVarianceAtPolynomial`.
The remaining analytic input is exactly the paper's six-step edge transport
bound, not a conclusion-shaped local-variance hypothesis. -/
lemma localVarianceOfPointsFromEdgeDeviation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (G : SubMeas (Polynomial params) ι)
    (hedge :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceOfPointsError params eps delta) :
    LocalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  refine
    { aggregateEdgeComparison := by
        exact sddRel_unit_family_of_pointwise strategy.state
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
      pointwiseLocalVarianceBound := by
        intro g
        exact pointConditionedLocalVarianceAtPolynomial_le_of_deviation
          params strategy G (hedge g)
      averagedLocalVarianceBound := by
        simpa [pointConditionedLocalVariance] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)
            (localVarianceOfPointsError params eps delta)
            (by
              intro g
              exact pointConditionedLocalVarianceAtPolynomial_le_of_deviation
                params strategy G (hedge g)) }

/-- Strict reduction for `lem:global-variance-of-points` on the strategy state.

The legacy wrapper `globalVarianceOfPoints` still accepts an already-proved
independent-points norm bound. This reduction proves that bound from the local
edge norm estimate by applying `lem:local-to-global` to the weighted state and
using the exact norm/variance identities above. The remaining missing analytic
input is therefore only the local edge transport estimate from
`lem:local-variance-of-points`. -/
lemma globalVarianceOfPointsFromLocalDeviation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (G : SubMeas (Polynomial params) ι)
    (hlocalDev :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceOfPointsError params eps delta) :
    GlobalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  let hlocal := localVarianceOfPointsFromEdgeDeviation params strategy eps delta G hlocalDev
  have hglobalNorm :
      ∀ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          globalVarianceOfPointsError params eps delta :=
    globalVarianceOfPoints_bound_of_local params eps delta
      (fun g => globalVarianceDeviationAtPolynomial params strategy strategy.state G g)
      (fun g => localVarianceDeviationAtPolynomial params strategy strategy.state G g)
      (globalVarianceDeviationAtPolynomial_le_m_localVarianceDeviationAtPolynomial
        params strategy G)
      hlocalDev
  have hglobalVariance :
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
        exact sddRel_unit_family_of_pointwise strategy.state
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
            simpa [globalVarianceDeviationAtPolynomial] using hglobalNorm g)
      pointwiseGlobalNormBound := hglobalNorm
      pointwiseExpansionTransfer := pointConditionedExpansionTransfer params strategy G
      pointwiseGlobalVarianceBound := hglobalVariance
      averagedGlobalVarianceBound := by
        simpa [pointConditionedGlobalVariance] using
          avgOver_polynomialDistribution_le_of_pointwise params
            (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)
            (globalVarianceOfPointsError params eps delta) hglobalVariance }

/-- Legacy wrapper for `lem:global-variance-of-points` with arbitrary bipartite
state and the independent-points norm bound supplied explicitly.

For the paper-faithful strategy state, prefer
`globalVarianceOfPointsFromLocalDeviation`, which derives the global norm and
variance consequences from the local edgewise weighted norm estimate. -/
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
