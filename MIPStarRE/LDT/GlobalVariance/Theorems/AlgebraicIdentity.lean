import MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results
import MIPStarRE.LDT.Preliminaries.CauchySchwarz
import MIPStarRE.LDT.Preliminaries.CompletionTransfer
import MIPStarRE.LDT.Preliminaries.ComparisonCore
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement
import MIPStarRE.LDT.Preliminaries.SelfConsistency.Extensions
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

/-! # Algebraic identities and variance reductions -/


lemma pointConditionedExpansionTransfer
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

lemma globalVarianceOfPoints_bound_of_local
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

lemma polynomialWeightSqrtOperator_conjTranspose
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    (polynomialWeightSqrtOperator params G g)ᴴ =
      polynomialWeightSqrtOperator params G g := by
  simpa [polynomialWeightSqrtOperator] using
    (CFC.sqrt_nonneg (G.outcome g)).isSelfAdjoint

lemma polynomialWeightSqrtOperator_mul_self
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    polynomialWeightSqrtOperator params G g *
        polynomialWeightSqrtOperator params G g =
      G.outcome g := by
  simpa [polynomialWeightSqrtOperator] using
    CFC.sqrt_mul_sqrt_self (G.outcome g) (G.outcome_pos g)

/-- The difference of the two weighted point-conditioned operators factors as
the tensor product of the point-operator difference and the square root of the
polynomial outcome. -/
lemma weightedPointConditionedOperator_sub
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

/-- The square of the weighted point-conditioned difference is the tensor of
the squared point-operator difference with the polynomial outcome. -/
lemma weightedPointConditionedOperator_sq
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
        simp [W, L]
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
            pointConditionedOutcomeOperatorAtPolynomial params strategy g v)ᴴ) :=
    leftTensor_conjTranspose _
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

end MIPStarRE.LDT.GlobalVariance
