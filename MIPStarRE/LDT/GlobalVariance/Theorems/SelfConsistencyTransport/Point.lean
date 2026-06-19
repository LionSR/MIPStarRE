import MIPStarRE.LDT.GlobalVariance.Theorems.SelfConsistencyTransport.Utilities

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! # Point-event self-consistency transport

This module contains the point self-consistency endpoints for the six-step
local-variance transport chain in `lem:local-variance-of-points`
(`expansion.tex`, lines 300--311).  These are the first and last `2δ`
moves; the point-line `2ε` moves live in `PointLine.lean`.
-/

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
  change SDDRel strategy.state (uniformDistribution (Point params))
    (IdxSubMeas.liftLeft
      (fun u : Point params =>
        postprocess (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement u)
          (fun a : Fq params => if a = g u then some () else none)))
    (IdxSubMeas.liftRight
      (fun u : Point params =>
        postprocess (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement u)
          (fun a : Fq params => if a = g u then some () else none)))
    (2 * delta)
  exact
    twoNotionsOfSelfConsistencyAfterEvaluation
      strategy.state strategy.permInvState
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      delta
      (fun u a => if a = g u then some () else none)
      hssc

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
    exact qSDDCore_optionUnit_some_le strategy.state (uniformDistribution (Point params))
      (fun u a => ((IdxSubMeas.liftLeft pointEvent) u).outcome a)
      (fun u a => ((IdxSubMeas.liftRight pointEvent) u).outcome a)
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

/-- Grouped-by-evaluation-value endpoint for the first self-consistency move in
`lem:local-variance-of-points`.

This is the sum-level analogue of `pointConditionedEventSelfConsistency_weighted_point`.
It follows the transport at `references/ldt-paper/expansion.tex`, lines
305--306, but first groups all polynomials with the same value `g(u)`.  The
multiplier family is `0` away from the fiber `a = g(u)` and is
`I ⊗ (G_g)^{1/2}` on that fiber, so the `cabApproxDelta` contraction is supplied
by the submeasurement inequality `∑_{g : g(u)=a} G_g ≤ I`.  Consequently the
bound is `2δ` for the polynomial sum, with no polynomial-cardinality loss. -/
lemma pointConditionedEventSelfConsistency_weighted_point_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      avgOver (uniformDistribution (Point params))
        (fun u =>
          let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
          ev strategy.state (Dᴴ * D))) ≤
      2 * delta := by
  classical
  let pointMeas : IdxSubMeas (Point params) (Fq params) ι :=
    fun u => (strategy.pointMeasurement u).toSubMeas
  have hbase :
      SDDRel strategy.state (uniformDistribution (Point params))
        (IdxSubMeas.liftLeft pointMeas)
        (IdxSubMeas.liftRight pointMeas)
        (2 * delta) := by
    have hssc :
        BipartiteSSCRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta := by
      refine ⟨?_⟩
      simpa [SymStrat.selfConsistencyFailureProbability] using
        hgood.selfConsistencyTest
    change SDDRel strategy.state (uniformDistribution (Point params))
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      (2 * delta)
    exact
      twoNotionsOfSelfConsistency strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta
        ⟨strategy.permInvState, hssc⟩
  have hbaseBound :
      avgOver (uniformDistribution (Point params))
        (fun u =>
          qSDDCore strategy.state
            (fun a : Fq params => ((IdxSubMeas.liftLeft pointMeas) u).outcome a)
            (fun a : Fq params => ((IdxSubMeas.liftRight pointMeas) u).outcome a)) ≤
        2 * delta := by
    simpa [sddError, qSDD, pointMeas] using hbase.squaredDistanceBound
  simpa using
    cabApproxDelta_sum_from_sdd params strategy.state
      (uniformDistribution (Point params))
      (fun u => u)
      (fun u a => ((IdxSubMeas.liftLeft pointMeas) u).outcome a)
      (fun u a => ((IdxSubMeas.liftRight pointMeas) u).outcome a)
      (fun u g => weightedPointConditionedOperatorAtPolynomial params strategy G g u)
      (fun u g => weightedPointConditionedRightOperatorAtPolynomial params strategy G g u)
      G (2 * delta) hbaseBound
      (by
        intro u g
        let A := pointConditionedOutcomeOperatorAtPolynomial params strategy g u
        let S := polynomialWeightSqrtOperator params G g
        change rightTensor (ι₁ := ι) S * leftTensor (ι₂ := ι) A = opTensor A S
        exact rightTensor_mul_leftTensor_eq_opTensor A S)
      (by
        intro u g
        let A := pointConditionedOutcomeOperatorAtPolynomial params strategy g u
        let S := polynomialWeightSqrtOperator params G g
        change rightTensor (ι₁ := ι) S * rightTensor (ι₁ := ι) A =
          rightTensor (ι₁ := ι) (S * A)
        exact rightTensor_mul_rightTensor S A)

/-- Sum-level first self-consistency endpoint on the hypercube-edge sampler.

This is the `u`-endpoint version of `references/ldt-paper/expansion.tex`, lines
305--306, after grouping polynomials by the common value `g(u)` before applying
`cabApproxDelta`.  It is the edge-distribution form of
`pointConditionedEventSelfConsistency_weighted_point_sum`. -/
lemma pointConditionedEventSelfConsistency_weighted_leftEdge_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      avgOver (rerandomizeCoord params)
        (fun uv =>
          let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g uv.1
          ev strategy.state (Dᴴ * D))) ≤
      2 * delta := by
  calc
    (∑ g : Polynomial params,
      avgOver (rerandomizeCoord params)
        (fun uv =>
          let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g uv.1
          ev strategy.state (Dᴴ * D)))
      = ∑ g : Polynomial params,
        avgOver (uniformDistribution (Point params))
          (fun u =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
            ev strategy.state (Dᴴ * D)) := by
          apply Finset.sum_congr rfl
          intro g _
          exact avgOver_rerandomizeCoord_fst params
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D))
    _ ≤ 2 * delta :=
        pointConditionedEventSelfConsistency_weighted_point_sum
          params strategy eps delta gamma hgood G

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

/-- Sum-level final self-consistency endpoint on the hypercube-edge sampler.

This is the `v`-endpoint version of `references/ldt-paper/expansion.tex`, lines
310--311.  The second marginal of `rerandomizeCoord` is uniform, and the squared
difference is unchanged after swapping the two endpoint operators. -/
lemma pointConditionedEventSelfConsistency_weighted_rightEdge_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      avgOver (rerandomizeCoord params)
        (fun uv =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g uv.2 -
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
          ev strategy.state (Dᴴ * D))) ≤
      2 * delta := by
  calc
    (∑ g : Polynomial params,
      avgOver (rerandomizeCoord params)
        (fun uv =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g uv.2 -
            weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
          ev strategy.state (Dᴴ * D)))
      = ∑ g : Polynomial params,
        avgOver (uniformDistribution (Point params))
          (fun u =>
            let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedOperatorAtPolynomial params strategy G g u
            ev strategy.state (Dᴴ * D)) := by
          apply Finset.sum_congr rfl
          intro g _
          exact avgOver_rerandomizeCoord_snd params
            (fun u =>
              let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D))
    _ = ∑ g : Polynomial params,
        avgOver (uniformDistribution (Point params))
          (fun u =>
            let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
              weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
            ev strategy.state (Dᴴ * D)) := by
          apply Finset.sum_congr rfl
          intro g _
          apply avgOver_congr
          intro u
          exact ev_adjoint_sub_swap strategy.state
            (weightedPointConditionedOperatorAtPolynomial params strategy G g u)
            (weightedPointConditionedRightOperatorAtPolynomial params strategy G g u)
    _ ≤ 2 * delta :=
        pointConditionedEventSelfConsistency_weighted_point_sum
          params strategy eps delta gamma hgood G


end MIPStarRE.LDT.GlobalVariance
