import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement
import MIPStarRE.LDT.GlobalVariance.MatrixRealization
import MIPStarRE.LDT.GlobalVariance.Theorems.Averaging
import MIPStarRE.LDT.GlobalVariance.Theorems.Statements

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
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

private lemma weightedGeneralizeBOperator_sub
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
        weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu =
      opTensor
        (generalizeBLeftOperatorAtPolynomial params strategy g qu -
          generalizeBRightOperatorAtPolynomial params strategy g qu)
        (polynomialWeightSqrtOperator params G g) := by
  simp [weightedGeneralizeBLeftOperatorAtPolynomial,
    weightedGeneralizeBRightOperatorAtPolynomial, opTensor_sub_left]

private lemma weightedGeneralizeBOperator_sq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
        weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
    Dᴴ * D =
      opTensor
        (((generalizeBLeftOperatorAtPolynomial params strategy g qu -
          generalizeBRightOperatorAtPolynomial params strategy g qu)ᴴ) *
            (generalizeBLeftOperatorAtPolynomial params strategy g qu -
              generalizeBRightOperatorAtPolynomial params strategy g qu))
        (G.outcome g) := by
  dsimp only
  rw [weightedGeneralizeBOperator_sub]
  rw [conjTranspose_opTensor, opTensor_mul]
  rw [polynomialWeightSqrtOperator_conjTranspose,
    polynomialWeightSqrtOperator_mul_self]

private lemma generalizeBCollisionOperatorAtPolynomial_proj
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    generalizeBCollisionOperatorAtPolynomial params strategy g qu *
        generalizeBCollisionOperatorAtPolynomial params strategy g qu =
      generalizeBCollisionOperatorAtPolynomial params strategy g qu := by
  change (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).outcome
      (some ()) *
    (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).outcome
      (some ()) =
    (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).outcome (some ())
  exact (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).proj (some ())

private lemma generalizeBCollisionOperatorAtPolynomial_conjTranspose
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) :
    (generalizeBCollisionOperatorAtPolynomial params strategy g qu)ᴴ =
      generalizeBCollisionOperatorAtPolynomial params strategy g qu := by
  change ((generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).outcome
      (some ()))ᴴ =
    (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).outcome (some ())
  exact (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).outcome_hermitian
    (some ())

private lemma generalizeB_right_event_implies_left_event
    (params : Parameters)
    [FieldModel params.q]
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params)
    (hline : pointOnLine (params := params) qu)
    (f : AxisLinePolynomial params)
    (hf : f.poly = (Polynomial.restrictToAxisParallelLine params g qu.1).poly) :
    f (axisParallelLineQuestionParameter qu) = g qu.2 := by
  rcases hline with ⟨t, ht⟩
  have hparam : axisParallelLineQuestionParameter qu = t := by
    cases qu with
    | mk ℓ u =>
        dsimp at ht ⊢
        subst ht
        simp
  have hf_eq : f = Polynomial.restrictToAxisParallelLine params g qu.1 :=
    AxisLinePolynomial.ext hf
  rw [hf_eq, hparam]
  simp [ht]

private lemma generalizeBLeftOperator_eq_right_add_collision
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params)
    (hline : pointOnLine (params := params) qu) :
    generalizeBLeftOperatorAtPolynomial params strategy g qu =
      generalizeBRightOperatorAtPolynomial params strategy g qu +
        generalizeBCollisionOperatorAtPolynomial params strategy g qu := by
  classical
  unfold generalizeBLeftOperatorAtPolynomial generalizeBRightOperatorAtPolynomial
    generalizeBCollisionOperatorAtPolynomial
  unfold generalizeBLeftEventSubMeasAtPolynomial generalizeBRightEventSubMeasAtPolynomial
    generalizeBCollisionEventSubMeasAtPolynomial
  cases qu with
  | mk ℓ u =>
      simp only [generalizeBCollisionEventProjMeasAtPolynomial, ProjMeas.postprocess,
        postprocess, Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases hq : x.poly = (Polynomial.restrictToAxisParallelLine params g ℓ).poly
      · have hp : x (axisParallelLineQuestionParameter (ℓ, u)) = g u := by
          exact generalizeB_right_event_implies_left_event params g (ℓ, u) hline x hq
        simp [hp, hq]
      · by_cases hp : x (axisParallelLineQuestionParameter (ℓ, u)) = g u <;> simp [hp, hq]

private lemma generalizeBLeft_sub_right_eq_collision
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params)
    (hline : pointOnLine (params := params) qu) :
    generalizeBLeftOperatorAtPolynomial params strategy g qu -
        generalizeBRightOperatorAtPolynomial params strategy g qu =
      generalizeBCollisionOperatorAtPolynomial params strategy g qu := by
  rw [generalizeBLeftOperator_eq_right_add_collision params strategy g qu hline]
  abel

private lemma generalizeBLineDifference_sq_eq_collision
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params)
    (hline : pointOnLine (params := params) qu) :
    ((generalizeBLeftOperatorAtPolynomial params strategy g qu -
        generalizeBRightOperatorAtPolynomial params strategy g qu)ᴴ) *
        (generalizeBLeftOperatorAtPolynomial params strategy g qu -
          generalizeBRightOperatorAtPolynomial params strategy g qu) =
      generalizeBCollisionOperatorAtPolynomial params strategy g qu := by
  rw [generalizeBLeft_sub_right_eq_collision params strategy g qu hline]
  rw [generalizeBCollisionOperatorAtPolynomial_conjTranspose,
    generalizeBCollisionOperatorAtPolynomial_proj]

private lemma generalizeBWeightedLineDifference_sq_eq_collision
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params)
    (qu : AxisParallelLineQuestion params)
    (hline : pointOnLine (params := params) qu) :
    let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
        weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
    Dᴴ * D =
      opTensor (generalizeBCollisionOperatorAtPolynomial params strategy g qu) (G.outcome g) := by
  dsimp only
  rw [weightedGeneralizeBOperator_sq]
  rw [generalizeBLineDifference_sq_eq_collision params strategy g qu hline]

/-- Projective expansion for the pointwise `lem:generalize-b` deviation.

For incident line questions, the right event `f = g|_ℓ` is a subevent of the
left event `f(u)=g(u)`.  Since `B^ℓ` is projective, the squared difference is
exactly the residual line-collision event `f(u)=g(u) ∧ f≠g|_ℓ`, with the
right-register square root collapsed to `G_g`. -/
lemma generalizeBDeviationAtPolynomial_eq_collisionResidual
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBDeviationAtPolynomial params strategy ψbi G g =
      generalizeBCollisionResidual params strategy ψbi G g := by
  unfold generalizeBDeviationAtPolynomial generalizeBCollisionResidual
  apply MIPStarRE.LDT.avgOver_congr_on_support
  intro qu hqu
  have hline : pointOnLine (params := params) qu := by
    simpa [axisParallelLineQuestionDistribution] using hqu
  dsimp only
  rw [generalizeBWeightedLineDifference_sq_eq_collision params strategy G g qu hline]

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

private lemma weightedNormDeviation_eq_pointConditionedDifferenceAvg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params)
    (𝒟 : Distribution (Point params × Point params)) :
    avgOver 𝒟 (fun uv =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
          weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
        ev strategy.state (Dᴴ * D)) =
      avgOver 𝒟 (fun uv =>
        ev (weightedPolynomialState params strategy G g)
          (pointDifferenceSquaredOperator
            (fun u => leftTensor (ι₂ := ι)
              (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)) uv.1 uv.2)) := by
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
  exact weightedNormDeviation_eq_pointConditionedDifferenceAvg params strategy G g
    (rerandomizeCoord params)

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
  exact weightedNormDeviation_eq_pointConditionedDifferenceAvg params strategy G g
    (independentPointPair params)

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
          linarith
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

private lemma generalizeB_of_pointwise
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (ψbi : QuantumState (ι × ι))
    (hpoint :
      ∀ g : Polynomial params,
        generalizeBDeviationAtPolynomial params strategy ψbi G g ≤ generalizeBError params) :
    GeneralizeBStatement params strategy ψbi G := by
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
  exact generalizeB_of_pointwise params strategy G ψbi hpoint

private lemma generalizeBLineCollisionTensorMass_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    0 ≤ ev strategy.state (opTensor ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
      (G.outcome g)) := by
  simpa [leftTensor_mul_rightTensor_eq_opTensor] using
    ev_leftTensor_mul_rightTensor_nonneg strategy.state
      ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome_pos f)
      (G.outcome_pos g)

/-- The total tensor mass left after summing over line answers is at most one.

This is the normalization half of `expansion.tex`, lines 286--288: the
left-register line measurement sums to its total operator, the right-register
operator is the single submeasurement outcome `G_g ≤ 1`, and the strategy state
is normalized. -/
private lemma generalizeBLineCollisionTensorMass_sum_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (ℓ : AxisParallelLine params) :
    (∑ f : AxisLinePolynomial params,
      ev strategy.state (opTensor ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
        (G.outcome g))) ≤ 1 := by
  let B := (strategy.axisParallelMeasurement ℓ).toSubMeas
  calc
    (∑ f : AxisLinePolynomial params,
      ev strategy.state (opTensor (B.outcome f) (G.outcome g)))
      = ev strategy.state (∑ f : AxisLinePolynomial params,
          opTensor (B.outcome f) (G.outcome g)) := by
          rw [ev_sum]
    _ = ev strategy.state (leftTensor (ι₂ := ι) B.total *
          rightTensor (ι₁ := ι) (G.outcome g)) := by
          congr 1
          calc
            (∑ f : AxisLinePolynomial params, opTensor (B.outcome f) (G.outcome g))
              = ∑ f : AxisLinePolynomial params,
                  leftTensor (ι₂ := ι) (B.outcome f) *
                    rightTensor (ι₁ := ι) (G.outcome g) := by
                    simp [leftTensor_mul_rightTensor_eq_opTensor]
            _ = (∑ f : AxisLinePolynomial params, leftTensor (ι₂ := ι) (B.outcome f)) *
                  rightTensor (ι₁ := ι) (G.outcome g) := by
                    rw [Finset.sum_mul]
            _ = leftTensor (ι₂ := ι) B.total * rightTensor (ι₁ := ι) (G.outcome g) := by
                    rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ B.outcome]
                    rw [B.sum_eq_total]
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          apply ev_mono strategy.state _ _
          calc
            leftTensor (ι₂ := ι) B.total * rightTensor (ι₁ := ι) (G.outcome g)
              = opTensor B.total (G.outcome g) := by
                  rw [leftTensor_mul_rightTensor_eq_opTensor]
            _ ≤ leftTensor (ι₂ := ι) B.total :=
                  opTensor_le_leftTensor (SubMeas.total_nonneg B) (SubMeas.outcome_le_one G g)
            _ ≤ 1 := leftTensor_le_one (ι₂ := ι) B.total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized

private lemma generalizeBLineCollisionCoefficient_le
    (params : Parameters)
    [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) (f : AxisLinePolynomial params) :
    avgOver (uniformDistribution (Fq params))
      (fun t =>
        if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
            f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
          (1 : Error)
        else 0) ≤ generalizeBError params := by
  classical
  let h := Polynomial.restrictToAxisParallelLine params g ℓ
  let δ := generalizeBError params
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ, generalizeBError]
    positivity
  by_cases hneq : f.poly ≠ h.poly
  · have hline := axisLinePolynomialAgreement_avg_le_mdq params f h hneq
    simpa [h, δ, generalizeBError, hneq] using hline
  · rw [show
        avgOver (uniformDistribution (Fq params))
          (fun t =>
            if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
              (1 : Error)
            else 0) = 0 by
          simpa [h, hneq] using (avgOver_zero (uniformDistribution (Fq params)))]
    exact hδ_nonneg

/-- The explicit line/parameter collision expansion is bounded by `m*d/q`.

This proves the Schwartz--Zippel and normalization parts of the residual estimate
from `expansion.tex`, lines 286--288.  The only remaining issue #753 work is the
finite reindexing identity equating
`generalizeBCollisionResidual` with
`generalizeBLineCollisionExpansion`. -/
lemma generalizeBLineCollisionExpansion_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBLineCollisionExpansion params strategy strategy.state G g ≤
      generalizeBError params := by
  classical
  let δ := generalizeBError params
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ, generalizeBError]
    positivity
  unfold generalizeBLineCollisionExpansion
  calc
    avgOver (uniformDistribution (AxisParallelLine params))
      (fun ℓ =>
        ∑ f : AxisLinePolynomial params,
          avgOver (uniformDistribution (Fq params))
            (fun t =>
              if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                  f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                (1 : Error)
              else 0) *
            ev strategy.state (opTensor
              ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
              (G.outcome g)))
      ≤ avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            ∑ f : AxisLinePolynomial params,
              δ * ev strategy.state (opTensor
                ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                (G.outcome g))) := by
            refine avgOver_mono _ _ _ ?_
            intro ℓ
            refine Finset.sum_le_sum ?_
            intro f _
            exact mul_le_mul_of_nonneg_right
              (by simpa [δ] using generalizeBLineCollisionCoefficient_le params g ℓ f)
              (generalizeBLineCollisionTensorMass_nonneg params strategy G g ℓ f)
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ => δ * ∑ f : AxisLinePolynomial params,
            ev strategy.state (opTensor
              ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
              (G.outcome g))) := by
            apply avgOver_congr
            intro ℓ
            rw [Finset.mul_sum]
    _ ≤ avgOver (uniformDistribution (AxisParallelLine params))
          (fun _ℓ => δ * 1) := by
            refine avgOver_mono _ _ _ ?_
            intro ℓ
            exact mul_le_mul_of_nonneg_left
              (generalizeBLineCollisionTensorMass_sum_le_one params strategy G g ℓ)
              hδ_nonneg
    _ = δ := by
            simpa using (avgOver_uniform_const (α := AxisParallelLine params) (c := δ))
    _ = generalizeBError params := rfl

/-- Strict reduction of the collision-residual estimate to the remaining finite
reindexing identity.

TODO(#753): prove the equality hypothesis by expanding
`ProjMeas.postprocess`, rewriting the incident-pair distribution as a uniform
line/parameter average, and commuting the finite sums. -/
lemma generalizeBCollisionResidual_le_of_lineExpansion_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (hreindex :
      generalizeBCollisionResidual params strategy strategy.state G g =
        generalizeBLineCollisionExpansion params strategy strategy.state G g) :
    generalizeBCollisionResidual params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [hreindex]
  exact generalizeBLineCollisionExpansion_le_error params strategy G g

/-- Strategy-state reduction for `lem:generalize-b` after the projective expansion.

This theorem removes the conclusion-shaped pointwise norm hypothesis from the
legacy wrapper.  The remaining input is the explicit line-collision residual
whose proof is the Schwartz--Zippel averaging step from
`expansion.tex`, lines 286--288. -/
lemma generalizeBFromCollisionResidual
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (hcollision :
      ∀ g : Polynomial params,
        generalizeBCollisionResidual params strategy strategy.state G g ≤
          generalizeBError params) :
    GeneralizeBStatement params strategy strategy.state G := by
  refine generalizeB_of_pointwise params strategy G strategy.state ?_
  intro g
  rw [generalizeBDeviationAtPolynomial_eq_collisionResidual]
  exact hcollision g

/-- Strategy-state reduction for `lem:generalize-b` from the explicit line/parameter
collision expansion.

This packages the strict #753 reduction: once the finite reindexing equality is
proved, the Schwartz--Zippel coefficient bound and tensor normalization bound
above supply the required collision residual estimate. -/
lemma generalizeBFromLineCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (hreindex :
      ∀ g : Polynomial params,
        generalizeBCollisionResidual params strategy strategy.state G g =
          generalizeBLineCollisionExpansion params strategy strategy.state G g) :
    GeneralizeBStatement params strategy strategy.state G := by
  refine generalizeBFromCollisionResidual params strategy G ?_
  intro g
  exact generalizeBCollisionResidual_le_of_lineExpansion_eq
    params strategy G g (hreindex g)

/-- The reverse `lem:generalize-b` step used at
`references/ldt-paper/expansion.tex`, line 309.

The paper first moves from the evaluated line event to the exact restriction
(line 308), then uses the same estimate in the reverse direction at the second
sampled point (line 309).  The squared-distance expression is unchanged by
swapping the two endpoints, because `(Y - X) = -(X - Y)`. -/
lemma generalizeBReversePointwiseBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (hgen : GeneralizeBStatement params strategy ψbi G)
    (g : Polynomial params) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu =>
        let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
          weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
        ev ψbi (Dᴴ * D)) ≤ generalizeBError params := by
  calc
    avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          ev ψbi (Dᴴ * D))
      = generalizeBDeviationAtPolynomial params strategy ψbi G g := by
          unfold generalizeBDeviationAtPolynomial
          apply avgOver_congr
          intro qu
          dsimp only
          let X := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          let Y := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
          have hdiff : Y - X = -(X - Y) := by
            simp [X, Y]
          have hconjDiff : Yᴴ - Xᴴ = -(Xᴴ - Yᴴ) := by
            abel
          have hsqExpanded : (Yᴴ - Xᴴ) * (Y - X) = (Xᴴ - Yᴴ) * (X - Y) := by
            calc
              (Yᴴ - Xᴴ) * (Y - X) =
                  (-(Xᴴ - Yᴴ)) * (Y - X) := by
                rw [hconjDiff]
              _ = (-(Xᴴ - Yᴴ)) * (-(X - Y)) := by rw [hdiff]
              _ = (Xᴴ - Yᴴ) * (X - Y) := by
                  rw [neg_mul, mul_neg, neg_neg]
          calc
            ev ψbi (((Y - X)ᴴ) * (Y - X)) =
                ev ψbi ((Yᴴ - Xᴴ) * (Y - X)) := by simp
            _ = ev ψbi ((Xᴴ - Yᴴ) * (X - Y)) := by
                exact congrArg (ev ψbi) hsqExpanded
            _ = ev ψbi (((X - Y)ᴴ) * (X - Y)) := by simp
    _ ≤ generalizeBError params := hgen.pointwiseNormBound g

/-- The post-triangle six-step transport error is absorbed by the paper's
`24(ε + δ + md/q)` slack from `lem:local-variance-of-points`.

This is only the scalar arithmetic after applying
`prop:triangle-inequality-for-approx_delta` with `k = 6` to the estimates at
`references/ldt-paper/expansion.tex`, lines 305--311; it does not assert the
transport estimates themselves. -/
lemma localVarianceTransportChainError_le_localVarianceOfPointsError
    (params : Parameters)
    [FieldModel params.q]
    {eps delta gamma : Error}
    (strategy : SymStrat params ι)
    (hgood : strategy.IsGood eps delta gamma) :
    localVarianceTransportChainError params eps delta ≤
      localVarianceOfPointsError params eps delta := by
  have heps_nonneg := eps_nonneg_of_isGood params strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params strategy hgood
  have hgen_nonneg : 0 ≤ generalizeBError params := by
    dsimp [generalizeBError]
    positivity
  dsimp [localVarianceTransportChainError, localVarianceOfPointsError]
  linarith

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

/-- Strategy-state reduction for `lem:local-variance-of-points` from the
post-triangle six-step transport-chain bound.

This replaces the final displayed edge estimate by the residual produced after
applying `prop:triangle-inequality-for-approx_delta` with `k = 6` to the six
paper steps (`2δ + 2ε + md/q + md/q + 2ε + 2δ`).  Thus the named residual is
`∀ g, localVarianceDeviationAtPolynomial … g ≤ localVarianceTransportChainError …`.
The absorption into the public `24(ε + δ + md/q)` statement is proved above. -/
lemma localVarianceOfPointsFromTransportChainBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (hchain :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceTransportChainError params eps delta) :
    LocalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  refine localVarianceOfPointsFromEdgeDeviation params strategy eps delta G ?_
  intro g
  exact le_trans (hchain g)
    (localVarianceTransportChainError_le_localVarianceOfPointsError
      params strategy hgood)

/-- Strategy-state global-variance reduction from the post-triangle six-step
local-variance transport-chain bound. -/
lemma globalVarianceOfPointsFromTransportChainBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (hchain :
      ∀ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
          localVarianceTransportChainError params eps delta) :
    GlobalVarianceOfPointsStatement params strategy strategy.state G eps delta := by
  refine globalVarianceOfPointsFromLocalDeviation params strategy eps delta G ?_
  intro g
  exact le_trans (hchain g)
    (localVarianceTransportChainError_le_localVarianceOfPointsError
      params strategy hgood)

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
