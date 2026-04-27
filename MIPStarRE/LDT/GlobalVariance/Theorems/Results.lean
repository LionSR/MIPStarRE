import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results
import MIPStarRE.LDT.Preliminaries.CauchySchwarz
import MIPStarRE.LDT.Preliminaries.ComparisonCore
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement
import MIPStarRE.LDT.Preliminaries.SelfConsistency.Extensions
import MIPStarRE.LDT.GlobalVariance.MatrixRealization
import MIPStarRE.LDT.GlobalVariance.Theorems.Averaging
import MIPStarRE.LDT.GlobalVariance.Theorems.Statements
import MIPStarRE.LDT.Test.StrategyFailures

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

/-- The finite reparametrization of incident axis-parallel line questions by a
line `ℓ` and affine parameter `t`, sending `(ℓ,t)` to `(ℓ, ℓ(t))`. -/
private noncomputable def axisParallelLineQuestionParameterEquiv (params : Parameters)
    [FieldModel params.q] :
    AxisParallelLine params × Fq params ≃
      {qu : AxisParallelLineQuestion params // pointOnLine (params := params) qu} where
  toFun := fun ℓt => ⟨(ℓt.1, ℓt.1.pointAt ℓt.2), ⟨ℓt.2, rfl⟩⟩
  invFun := fun qu => (qu.1.1, axisParallelLineQuestionParameter qu.1)
  left_inv := by
    intro ℓt
    cases ℓt with
    | mk ℓ t =>
        simp [axisParallelLineQuestionParameter_pointAt]
  right_inv := by
    intro qu
    rcases qu with ⟨qu, hqu⟩
    rcases qu with ⟨ℓ, u⟩
    rcases hqu with ⟨t, ht⟩
    apply Subtype.ext
    dsimp only
    have hparam : axisParallelLineQuestionParameter (ℓ, u) = t := by
      calc
        axisParallelLineQuestionParameter (ℓ, u) =
            axisParallelLineQuestionParameter (ℓ, ℓ.pointAt t) := by rw [ht]
        _ = t := axisParallelLineQuestionParameter_pointAt ℓ t
    ext <;> simp [hparam, ht]

/-- Reindex the axis-parallel line-question distribution as a uniform average over
line/parameter seeds `(ℓ,t)` with sampled point `u = ℓ(t)`.

This is the distributional bookkeeping used in `expansion.tex`, lines 281--288. -/
private lemma avgOver_axisParallelLineQuestionDistribution
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelLineQuestion params → Error) :
    avgOver (axisParallelLineQuestionDistribution params) f =
      avgOver (uniformDistribution (AxisParallelLine params × Fq params))
        (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2)) := by
  classical
  let e := axisParallelLineQuestionParameterEquiv params
  haveI :
      Nonempty {qu : AxisParallelLineQuestion params // pointOnLine (params := params) qu} := by
    exact ⟨e (Classical.choice
      (inferInstance : Nonempty (AxisParallelLine params × Fq params)))⟩
  calc
    avgOver (axisParallelLineQuestionDistribution params) f =
        avgOver (uniformDistribution
          {qu : AxisParallelLineQuestion params // pointOnLine (params := params) qu})
          (fun qu => f qu.1) := by
          let p : AxisParallelLineQuestion params → Prop := pointOnLine (params := params)
          have hcard : ((Finset.univ.filter p).card : Error) =
              (Fintype.card {qu : AxisParallelLineQuestion params // p qu} : Error) := by
            simp [p, Fintype.card_subtype]
          unfold axisParallelLineQuestionDistribution avgOver uniformDistribution
          dsimp only
          rw [← hcard]
          let support : Finset (AxisParallelLineQuestion params) := Finset.univ.filter p
          change (∑ x ∈ support,
              (if x ∈ support then 1 / (support.card : Error) else 0) * f x) =
            ∑ x : {qu : AxisParallelLineQuestion params // p qu},
              (1 / (support.card : Error)) * f x.1
          calc
            (∑ x ∈ support,
                (if x ∈ support then 1 / (support.card : Error) else 0) * f x)
              = ∑ x ∈ support, (1 / (support.card : Error)) * f x := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  simp [hx]
            _ = ∑ x : {qu : AxisParallelLineQuestion params // p qu},
                (1 / (support.card : Error)) * f x.1 := by
                  simpa [support, p] using
                    (Finset.sum_subtype_eq_sum_filter
                      (s := (Finset.univ : Finset (AxisParallelLineQuestion params)))
                      (f := fun qu : AxisParallelLineQuestion params =>
                        (1 / ((Finset.univ.filter p).card : Error)) * f qu)
                      (p := p)).symm
    _ = avgOver (uniformDistribution (AxisParallelLine params × Fq params))
          (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2)) := by
          have h := (avgOver_uniform_equiv (e := e.symm)
            (f := fun qu :
              {qu : AxisParallelLineQuestion params // pointOnLine (params := params) qu} =>
                f qu.1))
          simpa [e, axisParallelLineQuestionParameterEquiv] using h

/-- Expanding the postprocessed collision event at the seeded question
`(ℓ, ℓ(t))` gives the line-answer sum from `expansion.tex`, lines 283--286. -/
private lemma generalizeBCollisionSeed_integrand
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (ℓ : AxisParallelLine params) (t : Fq params) :
    ev ψbi (opTensor
        (generalizeBCollisionOperatorAtPolynomial params strategy g (ℓ, ℓ.pointAt t))
        (G.outcome g)) =
      ∑ f : AxisLinePolynomial params,
        (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
            f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
          (1 : Error)
        else 0) *
          ev ψbi (opTensor
            ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
            (G.outcome g)) := by
  classical
  unfold generalizeBCollisionOperatorAtPolynomial generalizeBCollisionEventSubMeasAtPolynomial
    generalizeBCollisionEventProjMeasAtPolynomial
  simp only [ProjMeas.postprocess, postprocess, axisParallelLineQuestionParameter_pointAt,
    Polynomial.restrictToAxisParallelLine_apply]
  rw [opTensor_sum_left_finset]
  rw [ev_finset_sum]
  simp [Finset.sum_filter]

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

/-- Commuting the uniform parameter average past the finite sum over line answers.

This is the purely finite-sum bookkeeping between the paper's seed average over
`(ℓ,t)` and the coefficient-weighted display in `expansion.tex`, lines 286--288.
The remaining #753 residual is now only the incident-question/postprocess equality
between `generalizeBCollisionResidual` and `generalizeBSeedCollisionExpansion`. -/
lemma generalizeBSeedCollisionExpansion_eq_lineCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBSeedCollisionExpansion params strategy ψbi G g =
      generalizeBLineCollisionExpansion params strategy ψbi G g := by
  classical
  unfold generalizeBSeedCollisionExpansion generalizeBLineCollisionExpansion
  calc
    avgOver (uniformDistribution (AxisParallelLine params × Fq params))
        (fun ℓt =>
          ∑ f : AxisLinePolynomial params,
            (if f ℓt.2 = (Polynomial.restrictToAxisParallelLine params g ℓt.1) ℓt.2 ∧
                f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓt.1).poly then
              (1 : Error)
            else 0) *
              ev ψbi (opTensor
                ((strategy.axisParallelMeasurement ℓt.1).toSubMeas.outcome f)
                (G.outcome g)))
      = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ => avgOver (uniformDistribution (Fq params))
            (fun t =>
              ∑ f : AxisLinePolynomial params,
                (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                    f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                  (1 : Error)
                else 0) *
                  ev ψbi (opTensor
                    ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                    (G.outcome g)))) := by
          exact avgOver_uniform_prod
            (α := AxisParallelLine params) (β := Fq params)
            (f := fun ℓ t =>
              ∑ f : AxisLinePolynomial params,
                (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                    f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                  (1 : Error)
                else 0) *
                  ev ψbi (opTensor
                    ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                    (G.outcome g)))
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            ∑ f : AxisLinePolynomial params,
              avgOver (uniformDistribution (Fq params))
                (fun t =>
                  (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                      f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                    (1 : Error)
                  else 0) *
                    ev ψbi (opTensor
                      ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                      (G.outcome g)))) := by
          apply avgOver_congr
          intro ℓ
          exact avgOver_sum (uniformDistribution (Fq params))
            (fun t f =>
              (if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                  f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
                (1 : Error)
              else 0) *
                ev ψbi (opTensor
                  ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
                  (G.outcome g)))
    _ = avgOver (uniformDistribution (AxisParallelLine params))
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
                  (G.outcome g))) := by
          apply avgOver_congr
          intro ℓ
          refine Finset.sum_congr rfl ?_
          intro f _
          rw [avgOver_mul_const]

/-- The incident-question collision residual is exactly the uniform line/parameter
seed expansion from `expansion.tex`, lines 286--288.

The proof reindexes the axis-parallel line-test distribution by `(ℓ,t)` with
sampled point `u = ℓ(t)`, then expands the `ProjMeas.postprocess` fiber for the
collision event `f(t) = g|_ℓ(t)` and `f ≠ g|_ℓ`. -/
lemma generalizeBCollisionResidual_eq_seedCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBCollisionResidual params strategy strategy.state G g =
      generalizeBSeedCollisionExpansion params strategy strategy.state G g := by
  classical
  unfold generalizeBCollisionResidual generalizeBSeedCollisionExpansion
  rw [avgOver_axisParallelLineQuestionDistribution]
  apply avgOver_congr
  intro ℓt
  cases ℓt with
  | mk ℓ t =>
      exact generalizeBCollisionSeed_integrand params strategy strategy.state G g ℓ t

/-- The explicit line/parameter collision expansion is bounded by `m*d/q`.

This proves the Schwartz--Zippel and normalization parts of the residual estimate
from `expansion.tex`, lines 286--288.  The preceding
`generalizeBCollisionResidual_eq_seedCollisionExpansion` theorem supplies the
incident-question/postprocess identity needed to apply this bound to the original
collision residual. -/
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

/-- The uniform line/parameter seed collision expansion is bounded by `m*d/q`.

The proof first commutes the finite seed average into the coefficient-weighted
line expansion, then applies the Schwartz--Zippel coefficient bound and tensor
normalization estimate above. -/
lemma generalizeBSeedCollisionExpansion_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBSeedCollisionExpansion params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBSeedCollisionExpansion_eq_lineCollisionExpansion]
  exact generalizeBLineCollisionExpansion_le_error params strategy G g

/-- The pointwise collision residual in `lem:generalize-b` is bounded by `m*d/q`.

This combines the incident-question reindexing with the seed/line expansion,
Schwartz--Zippel coefficient bound, and submeasurement-normalization estimate
from `expansion.tex`, lines 281--288. -/
lemma generalizeBCollisionResidual_le_error
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBCollisionResidual params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBCollisionResidual_eq_seedCollisionExpansion]
  exact generalizeBSeedCollisionExpansion_le_error params strategy G g

/-- Compatibility wrapper: a seed-expansion equality hypothesis also gives the
collision-residual estimate.

The equality is now provided by
`generalizeBCollisionResidual_eq_seedCollisionExpansion`; this lemma is retained
for callers that still pass the reindexing identity explicitly. -/
lemma generalizeBCollisionResidual_le_of_seedExpansion_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (hreindex :
      generalizeBCollisionResidual params strategy strategy.state G g =
        generalizeBSeedCollisionExpansion params strategy strategy.state G g) :
    generalizeBCollisionResidual params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [hreindex]
  exact generalizeBSeedCollisionExpansion_le_error params strategy G g

/-- Compatibility reduction from the older line-expansion equality hypothesis. -/
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
legacy wrapper.  The residual input is exactly the line-collision quantity
bounded above by `generalizeBCollisionResidual_le_error`, following
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

/-- Pointwise Schwartz--Zippel bound for the strategy-state form of
`lem:generalize-b`.

This is the paper's estimate at `expansion.tex`, lines 281--288, after the
projective expansion converts the squared norm into the collision residual. -/
lemma generalizeBPointwiseSchwartzZippel
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    generalizeBDeviationAtPolynomial params strategy strategy.state G g ≤
      generalizeBError params := by
  rw [generalizeBDeviationAtPolynomial_eq_collisionResidual]
  exact generalizeBCollisionResidual_le_error params strategy G g

/-- `lem:generalize-b` for the strategy state, with the pointwise
Schwartz--Zippel estimate discharged internally.  The good-strategy hypothesis is
kept in the statement to match the paper context of `expansion.tex`,
lines 271--288, although the algebraic Schwartz--Zippel proof itself does not
use `ε`, `δ`, or `γ`. -/
lemma generalizeBFromSchwartzZippel
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (_eps _delta _gamma : Error)
    (_hgood : strategy.IsGood _eps _delta _gamma)
    (G : SubMeas (Polynomial params) ι) :
    GeneralizeBStatement params strategy strategy.state G := by
  exact generalizeBFromCollisionResidual params strategy G
    (generalizeBCollisionResidual_le_error params strategy G)

/-- Strategy-state reduction for `lem:generalize-b` from the uniform line/parameter
seed collision expansion.

This compatibility route keeps the older explicit seed-expansion interface.
The equality input is now provided by
`generalizeBCollisionResidual_eq_seedCollisionExpansion`; callers that do not
need to supply it separately can use `generalizeBFromSchwartzZippel`. -/
lemma generalizeBFromSeedCollisionExpansion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (hreindex :
      ∀ g : Polynomial params,
        generalizeBCollisionResidual params strategy strategy.state G g =
          generalizeBSeedCollisionExpansion params strategy strategy.state G g) :
    GeneralizeBStatement params strategy strategy.state G := by
  refine generalizeBFromCollisionResidual params strategy G ?_
  intro g
  exact generalizeBCollisionResidual_le_of_seedExpansion_eq
    params strategy G g (hreindex g)

/-- Strategy-state reduction for `lem:generalize-b` from the explicit line/parameter
collision expansion.

This compatibility route keeps the older explicit line-expansion interface.
The seed-expansion route now proves the needed reindexing identity and pointwise
bound directly via `generalizeBCollisionResidual_le_error`. -/
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

/-- The first marginal of the rerandomized hypercube-edge distribution is uniform.
This is the finite-distribution form of the sampling statement in
`expansion.tex`, lines 300--302. -/
lemma avgOver_rerandomizeCoord_fst
    (params : Parameters) [FieldModel params.q]
    (f : Point params → Error) :
    avgOver (rerandomizeCoord params) (fun uv => f uv.1) =
      avgOver (uniformDistribution (Point params)) f := by
  classical
  unfold avgOver rerandomizeCoord uniformDistribution
  rw [Fintype.sum_prod_type]
  calc
    (∑ u : Point params, ∑ v : Point params,
        rerandomizeCoordWeight params u v * f u) =
        ∑ u : Point params, (∑ v : Point params, rerandomizeCoordWeight params u v) * f u := by
          refine Finset.sum_congr rfl ?_
          intro u _
          simpa using
            (Finset.sum_mul
              (s := (Finset.univ : Finset (Point params)))
              (f := fun v : Point params => rerandomizeCoordWeight params u v)
              (a := f u)).symm
    _ = ∑ u : Point params, (hypercubeVertexCount params : Error)⁻¹ * f u := by
          refine Finset.sum_congr rfl ?_
          intro u _
          simp [rerandomizeCoordWeight_rowSum]
    _ = ∑ u : Point params, (1 / (Fintype.card (Point params) : Error)) * f u := by
          simp [hypercubeVertexCount, one_div]

/-- The second marginal of the rerandomized hypercube-edge distribution is uniform.
This is the symmetric endpoint form of the sampling statement in `expansion.tex`,
lines 300--302. -/
lemma avgOver_rerandomizeCoord_snd
    (params : Parameters) [FieldModel params.q]
    (f : Point params → Error) :
    avgOver (rerandomizeCoord params) (fun uv => f uv.2) =
      avgOver (uniformDistribution (Point params)) f := by
  classical
  unfold avgOver rerandomizeCoord uniformDistribution
  rw [Fintype.sum_prod_type]
  calc
    (∑ u : Point params, ∑ v : Point params,
        rerandomizeCoordWeight params u v * f v) =
        ∑ v : Point params, ∑ u : Point params,
          rerandomizeCoordWeight params u v * f v := by
          rw [Finset.sum_comm]
    _ = ∑ v : Point params, (∑ u : Point params, rerandomizeCoordWeight params u v) * f v := by
          refine Finset.sum_congr rfl ?_
          intro v _
          simpa using
            (Finset.sum_mul
              (s := (Finset.univ : Finset (Point params)))
              (f := fun u : Point params => rerandomizeCoordWeight params u v)
              (a := f v)).symm
    _ = ∑ v : Point params, (hypercubeVertexCount params : Error)⁻¹ * f v := by
          refine Finset.sum_congr rfl ?_
          intro v _
          simp [rerandomizeCoordWeight_colSum]
    _ = ∑ v : Point params, (1 / (Fintype.card (Point params) : Error)) * f v := by
          simp [hypercubeVertexCount, one_div]

/-! ## Good-strategy interfaces for the local-variance transport chain -/

/-- The `2δ` self-consistency interface for the point event
`A^u_{g(u)}`.

This is the evaluated, two-outcome version of the first/last moves in
`lem:local-variance-of-points` (`expansion.tex`, lines 305--306 and 310--311):
postprocess the point measurement by the event `a = g(u)`, then apply
`prop:two-notions-of-self-consistency-after-evaluation` to the good-strategy
self-consistency branch. The remaining six-step proof still has to pull this
point-distribution estimate to the hypercube-edge sampling and weight it by
`(G_g)^{1/2}` via `prop:cab-approx-delta`. -/
lemma pointConditionedEventSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (g : Polynomial params) :
    SDDRel strategy.state (uniformDistribution (Point params))
      (IdxSubMeas.liftLeft
        (fun u : Point params =>
          pointConditionedEventSubMeasAtPolynomial params strategy g u))
      (IdxSubMeas.liftRight
        (fun u : Point params =>
          pointConditionedEventSubMeasAtPolynomial params strategy g u))
      (2 * delta) := by
  have hssc :
      BipartiteSSCRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
    refine ⟨?_⟩
    simpa [SymStrat.selfConsistencyFailureProbability] using
      hgood.selfConsistencyTest
  simpa [pointConditionedEventSubMeasAtPolynomial] using
    (twoNotionsOfSelfConsistencyAfterEvaluation
      strategy.state strategy.permInvState
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      delta
      (fun u a => if a = g u then some () else none)
      hssc)

private lemma rightPolynomialWeightSqrt_contraction
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    (rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g))ᴴ *
        rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g) ≤
      1 := by
  let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
  have hct : (rightTensor (ι₁ := ι) S)ᴴ = rightTensor (ι₁ := ι) Sᴴ := by
    simp [rightTensor, Matrix.conjTranspose_kronecker]
  calc
    (rightTensor (ι₁ := ι) S)ᴴ * rightTensor (ι₁ := ι) S =
        rightTensor (ι₁ := ι) (Sᴴ * S) := by
          rw [hct, rightTensor_mul_rightTensor]
    _ = rightTensor (ι₁ := ι) (G.outcome g) := by
          rw [show Sᴴ = S by simpa [S] using
            polynomialWeightSqrtOperator_conjTranspose (params := params) G g]
          rw [show S * S = G.outcome g by simpa [S] using
            polynomialWeightSqrtOperator_mul_self (params := params) G g]
    _ ≤ 1 := rightTensor_le_one (ι₁ := ι) (G.outcome_le_one g)

/-- The first self-consistency move in `lem:local-variance-of-points`, after
applying `prop:cab-approx-delta` with the multiplier `I ⊗ (G_g)^{1/2}` but
before pulling the point marginal to the hypercube-edge distribution.

This proves the weighted native-distribution version of `expansion.tex`,
lines 305--306:
`A^u_{g(u)} ⊗ (G_g)^{1/2} ≈_{2δ} I ⊗ (G_g)^{1/2} A^u_{g(u)}`. -/
lemma pointConditionedEventSelfConsistency_weighted_point
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (uniformDistribution (Point params))
      (fun u =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
        ev strategy.state (Dᴴ * D)) ≤
      2 * delta := by
  classical
  let pointEvent : IdxSubMeas (Point params) (Option Unit) ι :=
    fun u => pointConditionedEventSubMeasAtPolynomial params strategy g u
  let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
  let R : MIPStarRE.Quantum.Op (ι × ι) := rightTensor (ι₁ := ι) S
  let C : Point params → Unit → Unit → MIPStarRE.Quantum.Op (ι × ι) :=
    fun _ _ _ => R
  have hbase := pointConditionedEventSelfConsistency params strategy eps delta gamma hgood g
  have hbaseBound :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          qSDDCore strategy.state
            (fun a : Option Unit => ((IdxSubMeas.liftLeft pointEvent) u).outcome a)
            (fun a : Option Unit => ((IdxSubMeas.liftRight pointEvent) u).outcome a)) ≤
        2 * delta := by
    simpa [sddError, qSDD, pointEvent] using hbase.squaredDistanceBound
  have hselected_le :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          qSDDCore strategy.state
            (fun _ : Unit => ((IdxSubMeas.liftLeft pointEvent) u).outcome (some ()))
            (fun _ : Unit => ((IdxSubMeas.liftRight pointEvent) u).outcome (some ()))) ≤
        avgOver (uniformDistribution (Point params))
          (fun u =>
            qSDDCore strategy.state
              (fun a : Option Unit => ((IdxSubMeas.liftLeft pointEvent) u).outcome a)
              (fun a : Option Unit => ((IdxSubMeas.liftRight pointEvent) u).outcome a)) := by
    refine avgOver_mono _ _ _ ?_
    intro u
    unfold qSDDCore
    simpa using
      (Finset.single_le_sum
        (fun a _ => ev_adjoint_self_nonneg strategy.state
          (((IdxSubMeas.liftLeft pointEvent) u).outcome a -
            ((IdxSubMeas.liftRight pointEvent) u).outcome a))
        (Finset.mem_univ (some ())))
  have hAB :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          qSDDCore strategy.state
            (fun _ : Unit => ((IdxSubMeas.liftLeft pointEvent) u).outcome (some ()))
            (fun _ : Unit => ((IdxSubMeas.liftRight pointEvent) u).outcome (some ()))) ≤
        2 * delta := le_trans hselected_le hbaseBound
  have hC : ∀ u a, ∑ b : Unit, (C u a b)ᴴ * C u a b ≤ 1 := by
    intro u a
    simpa [C, R, S] using rightPolynomialWeightSqrt_contraction
      (params := params) (G := G) (g := g)
  have hcab :=
    cabApproxDelta strategy.state (uniformDistribution (Point params))
      (fun u _ => ((IdxSubMeas.liftLeft pointEvent) u).outcome (some ()))
      (fun u _ => ((IdxSubMeas.liftRight pointEvent) u).outcome (some ()))
      C (2 * delta) hAB hC
  simpa [qSDDCore, C, R, S, pointEvent, IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
    weightedPointConditionedOperatorAtPolynomial,
    weightedPointConditionedRightOperatorAtPolynomial,
    rightTensor_mul_leftTensor_eq_opTensor, rightTensor_mul_rightTensor] using hcab

/-- The first weighted self-consistency move on the actual hypercube-edge
sampling distribution `(u,v) ∼ C`.

This combines `pointConditionedEventSelfConsistency_weighted_point` with the
uniform first-marginal identity for `rerandomizeCoord`, closing the line-305 to
line-306 edge-distribution substep of `lem:local-variance-of-points`. -/
lemma pointConditionedEventSelfConsistency_weighted_leftEdge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (rerandomizeCoord params)
      (fun uv =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g uv.1
        ev strategy.state (Dᴴ * D)) ≤
      2 * delta := by
  calc
    avgOver (rerandomizeCoord params)
        (fun uv =>
          let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g uv.1
          ev strategy.state (Dᴴ * D))
      = avgOver (uniformDistribution (Point params))
          (fun u =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
            ev strategy.state (Dᴴ * D)) := by
          exact avgOver_rerandomizeCoord_fst params
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D))
    _ ≤ 2 * delta := pointConditionedEventSelfConsistency_weighted_point
      params strategy eps delta gamma hgood G g

private lemma ev_adjoint_sub_swap
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState κ) (X Y : MIPStarRE.Quantum.Op κ) :
    ev ψ (((Y - X)ᴴ) * (Y - X)) =
      ev ψ (((X - Y)ᴴ) * (X - Y)) := by
  have hdiff : Y - X = -(X - Y) := by
    simp
  have hconjDiff : Yᴴ - Xᴴ = -(Xᴴ - Yᴴ) := by
    abel
  have hsqExpanded : (Yᴴ - Xᴴ) * (Y - X) = (Xᴴ - Yᴴ) * (X - Y) := by
    calc
      (Yᴴ - Xᴴ) * (Y - X) = (-(Xᴴ - Yᴴ)) * (Y - X) := by
        rw [hconjDiff]
      _ = (-(Xᴴ - Yᴴ)) * (-(X - Y)) := by rw [hdiff]
      _ = (Xᴴ - Yᴴ) * (X - Y) := by
        rw [neg_mul, mul_neg, neg_neg]
  calc
    ev ψ (((Y - X)ᴴ) * (Y - X)) = ev ψ ((Yᴴ - Xᴴ) * (Y - X)) := by
      simp
    _ = ev ψ ((Xᴴ - Yᴴ) * (X - Y)) := by
      exact congrArg (ev ψ) hsqExpanded
    _ = ev ψ (((X - Y)ᴴ) * (X - Y)) := by
      simp

/-- The final weighted self-consistency move on the target endpoint of the
hypercube edge distribution.

This is the symmetric line-310 to line-311 substep of
`lem:local-variance-of-points`: after the second marginal reindexing,
`I ⊗ (G_g)^{1/2} A^v_{g(v)}` is `2δ`-close to
`A^v_{g(v)} ⊗ (G_g)^{1/2}`. -/
lemma pointConditionedEventSelfConsistency_weighted_rightEdge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (rerandomizeCoord params)
      (fun uv =>
        let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g uv.2 -
          weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
        ev strategy.state (Dᴴ * D)) ≤
      2 * delta := by
  calc
    avgOver (rerandomizeCoord params)
        (fun uv =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g uv.2 -
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
          ev strategy.state (Dᴴ * D))
      = avgOver (uniformDistribution (Point params))
          (fun u =>
            let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedOperatorAtPolynomial params strategy G g u
            ev strategy.state (Dᴴ * D)) := by
          exact avgOver_rerandomizeCoord_snd params
            (fun u =>
              let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D))
    _ = avgOver (uniformDistribution (Point params))
          (fun u =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
            ev strategy.state (Dᴴ * D)) := by
          apply avgOver_congr
          intro u
          exact ev_adjoint_sub_swap strategy.state
            (weightedPointConditionedOperatorAtPolynomial params strategy G g u)
            (weightedPointConditionedRightOperatorAtPolynomial params strategy G g u)
    _ ≤ 2 * delta := pointConditionedEventSelfConsistency_weighted_point
      params strategy eps delta gamma hgood G g

/-- The `ε` consistency interface for the point-line event at the base point of
an axis-parallel test sample.

For a sample `(u,i)`, the point side is the event `A^u_{g(u)}` and the line side
is the line-answer event obtained by evaluating the line polynomial at the base
parameter and testing equality with `g(u)`. This is the consistency input that
feeds the `2ε` approximation step at `expansion.tex`, line 307; the later
edge-transport proof still has to reindex from the base-point test sampling to
an arbitrary incident pair `(ℓ,u)` (using axis-line rebasing covariance) and then
apply `prop:simeq-to-approx`/`prop:cab-approx-delta`. -/
lemma axisParallelBaseEventConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (g : Polynomial params) :
    ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
      (fun s : AxisParallelTestSample params =>
        pointConditionedEventSubMeasAtPolynomial params strategy g s.1)
      (fun s : AxisParallelTestSample params =>
        postprocess (axisParallelLineAnswerFamily strategy s)
          (fun a : Fq params => if a = g s.1 then some () else none))
      eps := by
  have haxis :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy) eps := by
    refine ⟨?_⟩
    simpa [SymStrat.axisParallelFailureProbability] using
      hgood.axisParallelTest
  simpa [axisParallelPointAnswerFamily, pointConditionedEventSubMeasAtPolynomial] using
    (consRelDataProcessing_questionDependent
      strategy.state (uniformDistribution (AxisParallelTestSample params))
      (axisParallelPointAnswerFamily strategy)
      (axisParallelLineAnswerFamily strategy)
      eps
      (fun s a => if a = g s.1 then some () else none)
      haxis)

/-- The corresponding `2ε` approximation interface obtained from
`axisParallelBaseEventConsistency` by `prop:simeq-to-approx`.

This is the base-point form of the second move in the six-step chain.  The
remaining edge-transport assembly must still reindex it along the line-sampling
presentation where `v ∼ ℓ`, and then apply the square-root weighting used in the
operators `B^ℓ_[f(u)=g(u)] ⊗ (G_g)^{1/2}`. -/
lemma axisParallelBaseEventApproximation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (g : Polynomial params) :
    SDDRel strategy.state (uniformDistribution (AxisParallelTestSample params))
      (IdxSubMeas.liftLeft
        (fun s : AxisParallelTestSample params =>
          pointConditionedEventSubMeasAtPolynomial params strategy g s.1))
      (IdxSubMeas.liftRight
        (fun s : AxisParallelTestSample params =>
          postprocess (axisParallelLineAnswerFamily strategy s)
            (fun a : Fq params => if a = g s.1 then some () else none)))
      (2 * eps) := by
  let pointEvent : IdxSubMeas (AxisParallelTestSample params) (Option Unit) ι :=
    fun s => pointConditionedEventSubMeasAtPolynomial params strategy g s.1
  let lineEvent : IdxSubMeas (AxisParallelTestSample params) (Option Unit) ι :=
    fun s => postprocess (axisParallelLineAnswerFamily strategy s)
      (fun a : Fq params => if a = g s.1 then some () else none)
  have hpoint_complete : ∀ s, (pointEvent s).total = 1 := by
    intro s
    simp [pointEvent, pointConditionedEventSubMeasAtPolynomial,
      postprocess_total, (strategy.pointMeasurement s.1).total_eq_one]
  have hline_complete : ∀ s, (lineEvent s).total = 1 := by
    intro s
    simp [lineEvent, axisParallelLineAnswerFamily, postprocess_total,
      (strategy.axisParallelMeasurement { base := s.1, direction := s.2 }).total_eq_one]
  let pointMeas : IdxMeas (AxisParallelTestSample params) (Option Unit) ι :=
    fun s => (pointEvent s).toMeasurement (hpoint_complete s)
  let lineMeas : IdxMeas (AxisParallelTestSample params) (Option Unit) ι :=
    fun s => (lineEvent s).toMeasurement (hline_complete s)
  have hcons := axisParallelBaseEventConsistency params strategy eps delta gamma hgood g
  have hcons' :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas pointMeas)
        (IdxMeas.toIdxSubMeas lineMeas) eps := by
    simpa [pointMeas, lineMeas, pointEvent, lineEvent] using hcons
  have happrox :
      BipartiteSDDRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas pointMeas)
        (IdxMeas.toIdxSubMeas lineMeas) (2 * eps) :=
    simeqToApprox strategy.state (uniformDistribution (AxisParallelTestSample params))
      pointMeas lineMeas eps hcons'
  refine ⟨?_⟩
  simpa [pointMeas, lineMeas, pointEvent, lineEvent] using
    happrox.leftRightSquaredDistanceBound

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
