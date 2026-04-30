import MIPStarRE.LDT.GlobalVariance.Theorems.CollisionExpansion

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! # Good-strategy self-consistency transport

This module contains the good-strategy interfaces that establish the
`2δ` and `2ε` approximation steps for the six-step local-variance
transport chain in `lem:local-variance-of-points`
(`expansion.tex`, lines 300--311).
-/

lemma ev_adjoint_sub_swap
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
          exact ev_adjoint_sub_swap ψbi X Y
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
    simp
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

/-- Point-event measurement used by the base-point point-line consistency step. -/
private noncomputable def axisParallelBasePointEventMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) :
    IdxMeas (AxisParallelTestSample params) (Option Unit) ι :=
  fun s => (pointConditionedEventSubMeasAtPolynomial params strategy g s.1).toMeasurement (by
    unfold pointConditionedEventSubMeasAtPolynomial
    rw [postprocess_total]
    exact (strategy.pointMeasurement s.1).total_eq_one)

/-- Line-event measurement used by the base-point point-line consistency step. -/
private noncomputable def axisParallelBaseLineEventMeasurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) :
    IdxMeas (AxisParallelTestSample params) (Option Unit) ι :=
  fun s =>
    (postprocess (axisParallelLineAnswerFamily strategy s)
      (fun a : Fq params => if a = g s.1 then some () else none)).toMeasurement (by
      rw [postprocess_total]
      unfold axisParallelLineAnswerFamily
      rw [postprocess_total]
      exact (strategy.axisParallelMeasurement { base := s.1, direction := s.2 }).total_eq_one)

/-- Measurement-form bridge from `axisParallelBaseEventConsistency` for use with
`prop:simeq-to-approx`. -/
private lemma axisParallelBaseEventConsistency_measurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (g : Polynomial params) :
    ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
      (IdxMeas.toIdxSubMeas
        (axisParallelBasePointEventMeasurement params strategy g))
      (IdxMeas.toIdxSubMeas
        (axisParallelBaseLineEventMeasurement params strategy g))
      eps := by
  simpa [axisParallelBasePointEventMeasurement,
    axisParallelBaseLineEventMeasurement] using
    axisParallelBaseEventConsistency params strategy eps delta gamma hgood g

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
  let pointMeas := axisParallelBasePointEventMeasurement params strategy g
  let lineMeas := axisParallelBaseLineEventMeasurement params strategy g
  have hcons := axisParallelBaseEventConsistency_measurement
    params strategy eps delta gamma hgood g
  have happrox :
      BipartiteSDDRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas pointMeas)
        (IdxMeas.toIdxSubMeas lineMeas) (2 * eps) :=
    simeqToApprox strategy.state (uniformDistribution (AxisParallelTestSample params))
      pointMeas lineMeas eps hcons
  refine ⟨?_⟩
  simpa [pointMeas, lineMeas, axisParallelBasePointEventMeasurement,
    axisParallelBaseLineEventMeasurement] using
    happrox.leftRightSquaredDistanceBound

/-- The symmetric `2ε` approximation interface for the point-line event.

This is the orientation used in `expansion.tex`, lines 306--307 and 309--310:
the line event is placed on the left register and the point event on the right
register.  It is obtained from `axisParallelBaseEventConsistency` by first
swapping the two prover roles using the symmetric strategy state, then applying
`prop:simeq-to-approx`. -/
lemma axisParallelBaseEventApproximation_swapped
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (g : Polynomial params) :
    SDDRel strategy.state (uniformDistribution (AxisParallelTestSample params))
      (IdxSubMeas.liftLeft
        (fun s : AxisParallelTestSample params =>
          postprocess (axisParallelLineAnswerFamily strategy s)
            (fun a : Fq params => if a = g s.1 then some () else none)))
      (IdxSubMeas.liftRight
        (fun s : AxisParallelTestSample params =>
          pointConditionedEventSubMeasAtPolynomial params strategy g s.1))
      (2 * eps) := by
  let pointMeas := axisParallelBasePointEventMeasurement params strategy g
  let lineMeas := axisParallelBaseLineEventMeasurement params strategy g
  have hcons := axisParallelBaseEventConsistency_measurement
    params strategy eps delta gamma hgood g
  have hcons_swapped :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas lineMeas)
        (IdxMeas.toIdxSubMeas pointMeas) eps :=
    MIPStarRE.LDT.consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (AxisParallelTestSample params))
      (IdxMeas.toIdxSubMeas pointMeas) (IdxMeas.toIdxSubMeas lineMeas) eps hcons
  have happrox :
      BipartiteSDDRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas lineMeas)
        (IdxMeas.toIdxSubMeas pointMeas) (2 * eps) :=
    simeqToApprox strategy.state (uniformDistribution (AxisParallelTestSample params))
      lineMeas pointMeas eps hcons_swapped
  refine ⟨?_⟩
  simpa [pointMeas, lineMeas, axisParallelBasePointEventMeasurement,
    axisParallelBaseLineEventMeasurement] using
    happrox.leftRightSquaredDistanceBound

/-- The selected, square-root weighted point-line approximation on the native
axis-parallel base-point sample distribution.

After `prop:cab-approx-delta` with multiplier `I ⊗ (G_g)^{1/2}`, the swapped
base-event approximation gives the paper's line-306 to line-307 move at a
sample `(u,i)`: the line question is represented by the rebased line with base
`u` and direction `i`. -/
lemma axisParallelBaseEventApproximation_weighted_sample
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (uniformDistribution (AxisParallelTestSample params))
      (fun s =>
        let qu : AxisParallelLineQuestion params :=
          ({ base := s.1, direction := s.2 }, s.1)
        let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
        ev strategy.state (Dᴴ * D)) ≤
      2 * eps := by
  classical
  let pointEvent : IdxSubMeas (AxisParallelTestSample params) (Option Unit) ι :=
    fun s => pointConditionedEventSubMeasAtPolynomial params strategy g s.1
  let lineEvent : IdxSubMeas (AxisParallelTestSample params) (Option Unit) ι :=
    fun s => postprocess (axisParallelLineAnswerFamily strategy s)
      (fun a : Fq params => if a = g s.1 then some () else none)
  let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
  let R : MIPStarRE.Quantum.Op (ι × ι) := rightTensor (ι₁ := ι) S
  let C : AxisParallelTestSample params → Unit → Unit → MIPStarRE.Quantum.Op (ι × ι) :=
    fun _ _ _ => R
  have hbase := axisParallelBaseEventApproximation_swapped
    params strategy eps delta gamma hgood g
  have hbaseBound :
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          qSDDCore strategy.state
            (fun a : Option Unit => ((IdxSubMeas.liftLeft lineEvent) s).outcome a)
            (fun a : Option Unit => ((IdxSubMeas.liftRight pointEvent) s).outcome a)) ≤
        2 * eps := by
    simpa [sddError, qSDD, pointEvent, lineEvent] using hbase.squaredDistanceBound
  have hselected_le :
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          qSDDCore strategy.state
            (fun _ : Unit => ((IdxSubMeas.liftLeft lineEvent) s).outcome (some ()))
            (fun _ : Unit => ((IdxSubMeas.liftRight pointEvent) s).outcome (some ()))) ≤
        avgOver (uniformDistribution (AxisParallelTestSample params))
          (fun s =>
            qSDDCore strategy.state
              (fun a : Option Unit => ((IdxSubMeas.liftLeft lineEvent) s).outcome a)
              (fun a : Option Unit => ((IdxSubMeas.liftRight pointEvent) s).outcome a)) := by
    refine avgOver_mono _ _ _ ?_
    intro s
    unfold qSDDCore
    simpa using
      (Finset.single_le_sum
        (fun a _ => ev_adjoint_self_nonneg strategy.state
          (((IdxSubMeas.liftLeft lineEvent) s).outcome a -
            ((IdxSubMeas.liftRight pointEvent) s).outcome a))
        (Finset.mem_univ (some ())))
  have hAB :
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          qSDDCore strategy.state
            (fun _ : Unit => ((IdxSubMeas.liftLeft lineEvent) s).outcome (some ()))
            (fun _ : Unit => ((IdxSubMeas.liftRight pointEvent) s).outcome (some ()))) ≤
        2 * eps := le_trans hselected_le hbaseBound
  have hC : ∀ s a, ∑ b : Unit, (C s a b)ᴴ * C s a b ≤ 1 := by
    intro s a
    simpa [C, R, S] using rightPolynomialWeightSqrt_contraction
      (params := params) (G := G) (g := g)
  have hcab :=
    cabApproxDelta strategy.state (uniformDistribution (AxisParallelTestSample params))
      (fun s _ => ((IdxSubMeas.liftLeft lineEvent) s).outcome (some ()))
      (fun s _ => ((IdxSubMeas.liftRight pointEvent) s).outcome (some ()))
      C (2 * eps) hAB hC
  simpa [qSDDCore, C, R, S, pointEvent, lineEvent, IdxSubMeas.liftLeft,
    IdxSubMeas.liftRight, weightedGeneralizeBLeftOperatorAtPolynomial,
    weightedPointConditionedRightOperatorAtPolynomial, generalizeBLeftOperatorAtPolynomial,
    generalizeBLeftEventSubMeasAtPolynomial, axisParallelLineAnswerFamily,
    axisParallelLineQuestionParameter, subCoord, zeroCoord,
    rightTensor_mul_leftTensor_eq_opTensor, rightTensor_mul_rightTensor] using hcab

/-- Rebasing an incident axis-parallel line question at its sampled point does
not change the evaluated line event operator.

The left operator is the event `f(t)=g(ℓ(t))` for the line measurement on `ℓ`.
After rebasing `ℓ` at `t`, the sampled point is the new base point and the same
event is read as `f(0)=g(ℓ(t))`.  This is exactly the strategy's axis-parallel
measurement covariance, via `AxisParallelCovariantMeasurement.reparamInvariant`,
and is the operator-level reindexing used in `expansion.tex:300-307`. -/
private lemma generalizeBLeftOperatorAtPolynomial_rebaseAt_pointAt
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (ℓ : AxisParallelLine params) (t : Fq params) :
    generalizeBLeftOperatorAtPolynomial params strategy g (ℓ, ℓ.pointAt t) =
      generalizeBLeftOperatorAtPolynomial params strategy g
        (AxisParallelLine.rebaseAt ℓ t, ℓ.pointAt t) := by
  unfold generalizeBLeftOperatorAtPolynomial generalizeBLeftEventSubMeasAtPolynomial
  rw [axisParallelLineQuestionParameter_pointAt]
  have hparam_rebase :
      axisParallelLineQuestionParameter
        (AxisParallelLine.rebaseAt ℓ t, ℓ.pointAt t) = zeroCoord := by
    simp [axisParallelLineQuestionParameter, AxisParallelLine.rebaseAt, AxisParallelLine.pointAt,
      subCoord, zeroCoord]
  rw [hparam_rebase]
  have h := AxisParallelCovariantMeasurement.reparamInvariant strategy.axisParallelMeasurement
      ℓ t (g (ℓ.pointAt t))
  simp only [postprocess, ite_eq_left_iff, reduceCtorEq, imp_false, not_not] at h ⊢
  convert h.symm

/-- Weighted version of
`generalizeBLeftOperatorAtPolynomial_rebaseAt_pointAt`.

Tensoring the line event with the fixed polynomial weight `(G_g)^{1/2}` preserves
the rebasing equality.  This is the exact weighted operator identity needed to
transport the `2ε` base-point estimate to arbitrary incident line questions in
steps 2 and 5 of `lem:local-variance-of-points`. -/
private lemma weightedGeneralizeBLeftOperatorAtPolynomial_rebaseAt_pointAt
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (ℓ : AxisParallelLine params) (t : Fq params) :
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g (ℓ, ℓ.pointAt t) =
      weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
        (AxisParallelLine.rebaseAt ℓ t, ℓ.pointAt t) := by
  simp [weightedGeneralizeBLeftOperatorAtPolynomial,
    generalizeBLeftOperatorAtPolynomial_rebaseAt_pointAt]

/-- The weighted line-to-point approximation after reindexing the base-point test
sample to an arbitrary incident line question.

This is the paper's step 5 (`expansion.tex`, line 309--310), before coupling the
line question with the second endpoint of the hypercube-edge presentation: for
`v ∈ ℓ`, `B^ℓ_[f(v)=g(v)] ⊗ (G_g)^{1/2}` is `2ε`-close to
`I ⊗ (G_g)^{1/2} A^v_{g(v)}`. -/
lemma axisParallelPointLineConsistency_weighted_leftToRightLineQuestion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu =>
        let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
        ev strategy.state (Dᴴ * D)) ≤
      2 * eps := by
  let F : AxisParallelTestSample params → Error := fun s =>
    let qu : AxisParallelLineQuestion params := ({ base := s.1, direction := s.2 }, s.1)
    let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
      weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
    ev strategy.state (Dᴴ * D)
  calc
    avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
          ev strategy.state (Dᴴ * D))
      = avgOver (axisParallelLineQuestionDistribution params)
          (fun qu => F (qu.2, qu.1.direction)) := by
          apply MIPStarRE.LDT.avgOver_congr_on_support
          intro qu hqu
          have hline : pointOnLine (params := params) qu := by
            simpa [axisParallelLineQuestionDistribution] using hqu
          rcases qu with ⟨ℓ, u⟩
          rcases hline with ⟨t, ht⟩
          change ℓ.pointAt t = u at ht
          symm at ht
          subst u
          dsimp [F]
          rw [weightedGeneralizeBLeftOperatorAtPolynomial_rebaseAt_pointAt]
          simp [AxisParallelLine.rebaseAt]
    _ = avgOver (uniformDistribution (AxisParallelTestSample params)) F :=
        avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample params F
    _ ≤ 2 * eps := axisParallelBaseEventApproximation_weighted_sample
      params strategy eps delta gamma hgood G g

/-- The reverse weighted point-to-line approximation after incident-line
reindexing.

This is the paper's step 2 (`expansion.tex`, line 306--307):
`I ⊗ (G_g)^{1/2} A^u_{g(u)}` is `2ε`-close to
`B^ℓ_[f(u)=g(u)] ⊗ (G_g)^{1/2}` for an incident line question `(ℓ,u)`. -/
lemma axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu =>
        let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
          weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
        ev strategy.state (Dᴴ * D)) ≤
      2 * eps := by
  calc
    avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          ev strategy.state (Dᴴ * D))
      = avgOver (axisParallelLineQuestionDistribution params)
          (fun qu =>
            let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
            ev strategy.state (Dᴴ * D)) := by
          apply avgOver_congr
          intro qu
          exact ev_adjoint_sub_swap strategy.state
            (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
            (weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2)
    _ ≤ 2 * eps := axisParallelPointLineConsistency_weighted_leftToRightLineQuestion
      params strategy eps delta gamma hgood G g

end MIPStarRE.LDT.GlobalVariance
