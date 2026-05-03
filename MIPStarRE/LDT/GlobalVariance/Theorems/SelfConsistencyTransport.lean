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

private lemma rightPolynomialWeightSqrt_grouped_contraction
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι)
    (u : Point params) (a : Fq params) :
    ∑ g : Polynomial params,
        (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
          else 0)ᴴ *
          (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
            else 0) ≤ 1 := by
  classical
  let fiber : Finset (Polynomial params) := Finset.univ.filter fun g => a = g u
  have hfiber_le_total :
      ∑ g ∈ fiber, G.outcome g ≤ G.total := by
    calc
      ∑ g ∈ fiber, G.outcome g ≤ ∑ g : Polynomial params, G.outcome g := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by
            intro g hg
            exact Finset.mem_univ g)
          (by
            intro g _ _hg
            exact G.outcome_pos g)
      _ = G.total := G.sum_eq_total
  calc
    ∑ g : Polynomial params,
        (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
          else 0)ᴴ *
          (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
            else 0)
      = ∑ g ∈ fiber, rightTensor (ι₁ := ι) (G.outcome g) := by
          dsimp [fiber]
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro g _
          by_cases hg : a = g u
          · simp [hg, polynomialWeightSqrtOperator_conjTranspose,
              polynomialWeightSqrtOperator_mul_self, rightTensor_mul_rightTensor]
          · simp [hg]
    _ = rightTensor (ι₁ := ι) (∑ g ∈ fiber, G.outcome g) := by
          rw [rightTensor_finset_sum]
    _ ≤ 1 := rightTensor_le_one (ι₁ := ι) (le_trans hfiber_le_total G.total_le_one)

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
  let C : Point params → Fq params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun u a g =>
      if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
      else 0
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
    simpa [pointMeas] using
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
  have hC :
      ∀ u a, ∑ g : Polynomial params, (C u a g)ᴴ * C u a g ≤ 1 := by
    intro u a
    simpa [C] using rightPolynomialWeightSqrt_grouped_contraction params G u a
  have hcab :=
    cabApproxDelta strategy.state (uniformDistribution (Point params))
      (fun u a => ((IdxSubMeas.liftLeft pointMeas) u).outcome a)
      (fun u a => ((IdxSubMeas.liftRight pointMeas) u).outcome a)
      C (2 * delta) hbaseBound hC
  calc
    (∑ g : Polynomial params,
      avgOver (uniformDistribution (Point params))
        (fun u =>
          let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
          ev strategy.state (Dᴴ * D)))
      = avgOver (uniformDistribution (Point params))
          (fun u =>
            qSDDCore strategy.state
              (fun ag : Fq params × Polynomial params =>
                C u ag.1 ag.2 * ((IdxSubMeas.liftLeft pointMeas) u).outcome ag.1)
              (fun ag : Fq params × Polynomial params =>
                C u ag.1 ag.2 * ((IdxSubMeas.liftRight pointMeas) u).outcome ag.1)) := by
          rw [← avgOver_sum]
          apply avgOver_congr
          intro u
          unfold qSDDCore
          rw [Fintype.sum_prod_type]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro g _
          symm
          let term : Fq params → Error := fun x =>
            ev strategy.state
              ((((C u x g * ((IdxSubMeas.liftLeft pointMeas) u).outcome x) -
                    (C u x g * ((IdxSubMeas.liftRight pointMeas) u).outcome x))ᴴ) *
                ((C u x g * ((IdxSubMeas.liftLeft pointMeas) u).outcome x) -
                  (C u x g * ((IdxSubMeas.liftRight pointMeas) u).outcome x)))
          change (∑ x : Fq params, term x) =
            ev strategy.state
              (((weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                  weightedPointConditionedRightOperatorAtPolynomial params strategy G g u)ᴴ) *
                (weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                  weightedPointConditionedRightOperatorAtPolynomial params strategy G g u))
          calc
            (∑ x : Fq params, term x) = term (g u) := by
              refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fq params)))
                (a := g u) ?_ ?_
              · intro x _ hx
                simpa [term, C, hx] using ev_zero strategy.state
              · intro hmissing
                exact False.elim (hmissing (Finset.mem_univ (g u)))
            _ = ev strategy.state
                (((weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                    weightedPointConditionedRightOperatorAtPolynomial params strategy G g u)ᴴ) *
                  (weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                    weightedPointConditionedRightOperatorAtPolynomial params strategy G g u)) := by
              let A := pointConditionedOutcomeOperatorAtPolynomial params strategy g u
              let S := polynomialWeightSqrtOperator params G g
              have hleft :
                  rightTensor (ι₁ := ι) S *
                      ((IdxSubMeas.liftLeft pointMeas) u).outcome (g u) =
                    weightedPointConditionedOperatorAtPolynomial params strategy G g u := by
                change rightTensor (ι₁ := ι) S * leftTensor (ι₂ := ι) A = opTensor A S
                exact rightTensor_mul_leftTensor_eq_opTensor A S
              have hright :
                  rightTensor (ι₁ := ι) S *
                      ((IdxSubMeas.liftRight pointMeas) u).outcome (g u) =
                    weightedPointConditionedRightOperatorAtPolynomial params strategy G g u := by
                change rightTensor (ι₁ := ι) S * rightTensor (ι₁ := ι) A =
                  rightTensor (ι₁ := ι) (S * A)
                exact rightTensor_mul_rightTensor S A
              let X := weightedPointConditionedOperatorAtPolynomial params strategy G g u
              let Y := weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              calc
                term (g u) =
                    ev strategy.state
                      (((rightTensor (ι₁ := ι) S *
                            ((IdxSubMeas.liftLeft pointMeas) u).outcome (g u) -
                          rightTensor (ι₁ := ι) S *
                            ((IdxSubMeas.liftRight pointMeas) u).outcome (g u))ᴴ) *
                        (rightTensor (ι₁ := ι) S *
                            ((IdxSubMeas.liftLeft pointMeas) u).outcome (g u) -
                          rightTensor (ι₁ := ι) S *
                            ((IdxSubMeas.liftRight pointMeas) u).outcome (g u))) := by
                        simp [term, C, S]
                _ = ev strategy.state (((X - Y)ᴴ) * (X - Y)) := by
                    rw [hleft, hright]
    _ ≤ 2 * delta := hcab

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

/-! ## Sum-form (cardinality-free) `2ε` axis-parallel consistency endpoints

The lemmas below are the polynomial-sum (i.e. unnormalized `∑_g`) analogues of
the per-`g` `2ε` endpoints above.  They keep the answer space at `Fq params`
rather than postprocessing to the per-`g` `Option Unit` event, then group
polynomials by the common value `g(u)` via the `cabApproxDelta` multiplier
`if a = g s.1 then rightTensor (G_g)^{1/2} else 0`.  Combined with the
submeasurement contraction `∑_{g : g(u) = a} G_g ≤ I` from
`rightPolynomialWeightSqrt_grouped_contraction`, this gives `2ε` for the full
polynomial sum, with no polynomial-cardinality loss.  These are the steps 2 and
5 sum-level inputs to `eq:equivalent-local-variance`
(`references/ldt-paper/expansion.tex:317--321`).
-/

private noncomputable def axisParallelPointAnswerMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s => (axisParallelPointAnswerFamily strategy s).toMeasurement (by
    unfold axisParallelPointAnswerFamily
    exact (strategy.pointMeasurement s.1).total_eq_one)

private noncomputable def axisParallelLineAnswerMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) :
    IdxMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s => (axisParallelLineAnswerFamily strategy s).toMeasurement (by
    unfold axisParallelLineAnswerFamily
    rw [postprocess_total]
    exact (strategy.axisParallelMeasurement
      { base := s.1, direction := s.2 }).total_eq_one)

private lemma axisParallelAnswerConsistency_measurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
      (IdxMeas.toIdxSubMeas (axisParallelPointAnswerMeasurement params strategy))
      (IdxMeas.toIdxSubMeas (axisParallelLineAnswerMeasurement params strategy))
      eps := by
  have haxis :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy) eps := by
    refine ⟨?_⟩
    simpa [SymStrat.axisParallelFailureProbability] using
      hgood.axisParallelTest
  simpa [axisParallelPointAnswerMeasurement, axisParallelLineAnswerMeasurement,
    IdxMeas.toIdxSubMeas] using haxis

/-- The lifted line-answer family outcome at value `a = g(s.1)` reduces to the
left-tensor of the `lem:generalize-b` left operator at the incident question
`(ℓ, s.1)` with `ℓ = {base := s.1, direction := s.2}`.

This is the operator identity bridging the un-postprocessed `Fq params`-valued
line answer family to the per-`g` line operator used in
`weightedGeneralizeBLeftOperatorAtPolynomial`.  The two sides differ only by
rewriting `axisParallelLineQuestionParameter` at the diagonal sample point. -/
private lemma liftLeft_lineAnswerMeasurement_outcome_at_g
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (s : AxisParallelTestSample params) :
    ((IdxSubMeas.liftLeft
        (IdxMeas.toIdxSubMeas (axisParallelLineAnswerMeasurement params strategy))) s).outcome
        (g s.1) =
      leftTensor (ι₂ := ι)
        (generalizeBLeftOperatorAtPolynomial params strategy g
          ({ base := s.1, direction := s.2 }, s.1)) := by
  classical
  simp only [IdxSubMeas.liftLeft, IdxMeas.toIdxSubMeas,
    axisParallelLineAnswerMeasurement, axisParallelLineAnswerFamily,
    generalizeBLeftOperatorAtPolynomial, generalizeBLeftEventSubMeasAtPolynomial,
    axisParallelLineQuestionParameter, subCoord, zeroCoord,
    SubMeas.toMeasurement_toSubMeas, mkLeftPlacedSubMeas_outcome, postprocess]
  congr 1
  congr 1
  apply Finset.ext
  intro a
  simp

/-- The lifted point-answer family outcome at value `a = g(s.1)` reduces to the
right-tensor of the `point-conditioned` operator at base point `s.1`. -/
private lemma liftRight_pointAnswerMeasurement_outcome_at_g
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (s : AxisParallelTestSample params) :
    ((IdxSubMeas.liftRight
        (IdxMeas.toIdxSubMeas (axisParallelPointAnswerMeasurement params strategy))) s).outcome
        (g s.1) =
      rightTensor (ι₁ := ι)
        (pointConditionedOutcomeOperatorAtPolynomial params strategy g s.1) := by
  simp [IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas,
    axisParallelPointAnswerMeasurement, axisParallelPointAnswerFamily,
    pointConditionedOutcomeOperatorAtPolynomial,
    SubMeas.toMeasurement_toSubMeas, mkRightPlacedSubMeas_outcome]

/-- Sum-level base-sample form of the `2ε` axis-parallel consistency move,
oriented with the line event on the left register and the point event on the
right register.

This is the polynomial-sum version of
`axisParallelBaseEventApproximation_weighted_sample`: instead of fixing `g`
and postprocessing both sides to the `Option Unit` event `a = g(u)`, we keep
the full `Fq params` answer space and use the multiplier
`C s a g := if a = g s.1 then rightTensor (G_g)^{1/2} else 0` inside
`prop:cab-approx-delta`.  The contraction
`∀ s a, ∑_g (C s a g)ᴴ * (C s a g) ≤ I` is supplied by
`rightPolynomialWeightSqrt_grouped_contraction`, which uses the submeasurement
inequality `∑_{g : g(s.1) = a} G_g ≤ I`.  Consequently the bound is `2ε` for
the polynomial sum, with no polynomial-cardinality loss. -/
lemma axisParallelBaseEventApproximation_weighted_sample_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          let qu : AxisParallelLineQuestion params :=
            ({ base := s.1, direction := s.2 }, s.1)
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
          ev strategy.state (Dᴴ * D))) ≤
      2 * eps := by
  classical
  let pointMeas : IdxMeas (AxisParallelTestSample params) (Fq params) ι :=
    axisParallelPointAnswerMeasurement params strategy
  let lineMeas : IdxMeas (AxisParallelTestSample params) (Fq params) ι :=
    axisParallelLineAnswerMeasurement params strategy
  let C : AxisParallelTestSample params → Fq params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun s a g =>
      if a = g s.1 then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
      else 0
  have hcons :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas pointMeas) (IdxMeas.toIdxSubMeas lineMeas) eps :=
    axisParallelAnswerConsistency_measurement params strategy eps delta gamma hgood
  have hcons_swapped :
      ConsRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas lineMeas) (IdxMeas.toIdxSubMeas pointMeas) eps :=
    MIPStarRE.LDT.consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (AxisParallelTestSample params))
      (IdxMeas.toIdxSubMeas pointMeas) (IdxMeas.toIdxSubMeas lineMeas) eps hcons
  have happrox :
      BipartiteSDDRel strategy.state (uniformDistribution (AxisParallelTestSample params))
        (IdxMeas.toIdxSubMeas lineMeas) (IdxMeas.toIdxSubMeas pointMeas) (2 * eps) :=
    simeqToApprox strategy.state (uniformDistribution (AxisParallelTestSample params))
      lineMeas pointMeas eps hcons_swapped
  have hbase :
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          qSDDCore strategy.state
            (fun a : Fq params =>
              ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome a)
            (fun a : Fq params =>
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome a)) ≤
        2 * eps := by
    simpa [sddError, qSDD] using happrox.leftRightSquaredDistanceBound
  have hC :
      ∀ s a, ∑ g : Polynomial params, (C s a g)ᴴ * C s a g ≤ 1 := by
    intro s a
    simpa [C] using rightPolynomialWeightSqrt_grouped_contraction params G s.1 a
  have hcab :=
    cabApproxDelta strategy.state (uniformDistribution (AxisParallelTestSample params))
      (fun s a => ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome a)
      (fun s a => ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome a)
      C (2 * eps) hbase hC
  calc
    (∑ g : Polynomial params,
      avgOver (uniformDistribution (AxisParallelTestSample params))
        (fun s =>
          let qu : AxisParallelLineQuestion params :=
            ({ base := s.1, direction := s.2 }, s.1)
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
          ev strategy.state (Dᴴ * D)))
      = avgOver (uniformDistribution (AxisParallelTestSample params))
          (fun s =>
            qSDDCore strategy.state
              (fun ag : Fq params × Polynomial params =>
                C s ag.1 ag.2 *
                  ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome ag.1)
              (fun ag : Fq params × Polynomial params =>
                C s ag.1 ag.2 *
                  ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome ag.1)) := by
          rw [← avgOver_sum]
          apply avgOver_congr
          intro s
          unfold qSDDCore
          rw [Fintype.sum_prod_type]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro g _
          symm
          let term : Fq params → Error := fun x =>
            ev strategy.state
              ((((C s x g *
                    ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome x) -
                  (C s x g *
                    ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome x))ᴴ) *
                ((C s x g *
                    ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome x) -
                  (C s x g *
                    ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome x)))
          let qu : AxisParallelLineQuestion params :=
            ({ base := s.1, direction := s.2 }, s.1)
          change (∑ x : Fq params, term x) =
            ev strategy.state
              (((weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                  weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1)ᴴ) *
                (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                  weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1))
          calc
            (∑ x : Fq params, term x) = term (g s.1) := by
              refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fq params)))
                (a := g s.1) ?_ ?_
              · intro x _ hx
                simpa [term, C, hx] using ev_zero strategy.state
              · intro hmissing
                exact False.elim (hmissing (Finset.mem_univ (g s.1)))
            _ = ev strategy.state
                (((weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                    weightedPointConditionedRightOperatorAtPolynomial
                      params strategy G g s.1)ᴴ) *
                  (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                    weightedPointConditionedRightOperatorAtPolynomial
                      params strategy G g s.1)) := by
              let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
              let A : MIPStarRE.Quantum.Op ι :=
                pointConditionedOutcomeOperatorAtPolynomial params strategy g s.1
              let L : MIPStarRE.Quantum.Op ι :=
                generalizeBLeftOperatorAtPolynomial params strategy g qu
              have hline_outcome :
                  ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome (g s.1) =
                    leftTensor (ι₂ := ι) L :=
                liftLeft_lineAnswerMeasurement_outcome_at_g params strategy g s
              have hpoint_outcome :
                  ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome (g s.1) =
                    rightTensor (ι₁ := ι) A :=
                liftRight_pointAnswerMeasurement_outcome_at_g params strategy g s
              have hline :
                  rightTensor (ι₁ := ι) S *
                      ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome (g s.1) =
                    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu := by
                rw [hline_outcome]
                show rightTensor (ι₁ := ι) S * leftTensor (ι₂ := ι) L = opTensor L S
                exact rightTensor_mul_leftTensor_eq_opTensor L S
              have hpoint :
                  rightTensor (ι₁ := ι) S *
                      ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome (g s.1) =
                    weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1 := by
                rw [hpoint_outcome]
                show rightTensor (ι₁ := ι) S * rightTensor (ι₁ := ι) A =
                  rightTensor (ι₁ := ι) (S * A)
                exact rightTensor_mul_rightTensor S A
              let X := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              let Y := weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
              calc
                term (g s.1) =
                    ev strategy.state
                      (((rightTensor (ι₁ := ι) S *
                            ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome
                              (g s.1) -
                          rightTensor (ι₁ := ι) S *
                            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome
                              (g s.1))ᴴ) *
                        (rightTensor (ι₁ := ι) S *
                            ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome
                              (g s.1) -
                          rightTensor (ι₁ := ι) S *
                            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome
                              (g s.1))) := by
                        simp [term, C, S]
                _ = ev strategy.state (((X - Y)ᴴ) * (X - Y)) := by
                    rw [hline, hpoint]
    _ ≤ 2 * eps := hcab

/-- Sum-level form of the weighted line-to-point approximation
(`expansion.tex:309--310`, paper step 5) on the
`axisParallelLineQuestionDistribution` distribution.

This is the polynomial-sum analogue of
`axisParallelPointLineConsistency_weighted_leftToRightLineQuestion`.  After
reindexing the line-question sampling along its incident-pair structure (using
the existing rebasing covariance for the line operator), it reduces to the
sum-level base-sample bound `axisParallelBaseEventApproximation_weighted_sample_sum`. -/
lemma axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
          ev strategy.state (Dᴴ * D))) ≤
      2 * eps := by
  classical
  let F : Polynomial params → AxisParallelTestSample params → Error := fun g s =>
    let qu : AxisParallelLineQuestion params := ({ base := s.1, direction := s.2 }, s.1)
    let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
      weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
    ev strategy.state (Dᴴ * D)
  calc
    (∑ g : Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
            weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
          ev strategy.state (Dᴴ * D)))
      = ∑ g : Polynomial params,
          avgOver (axisParallelLineQuestionDistribution params)
            (fun qu => F g (qu.2, qu.1.direction)) := by
          refine Finset.sum_congr rfl ?_
          intro g _
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
    _ = ∑ g : Polynomial params,
          avgOver (uniformDistribution (AxisParallelTestSample params)) (F g) := by
          refine Finset.sum_congr rfl ?_
          intro g _
          exact avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample
            params (F g)
    _ ≤ 2 * eps :=
        axisParallelBaseEventApproximation_weighted_sample_sum
          params strategy eps delta gamma hgood G

/-- Sum-level form of the reverse weighted point-to-line approximation
(`expansion.tex:306--307`, paper step 2) on the
`axisParallelLineQuestionDistribution` distribution.

This is the polynomial-sum analogue of
`axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion`.  Each
summand is unchanged after swapping the two endpoint operators, so this reduces
to `axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum`. -/
lemma axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι) :
    (∑ g : Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          ev strategy.state (Dᴴ * D))) ≤
      2 * eps := by
  calc
    (∑ g : Polynomial params,
      avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2 -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          ev strategy.state (Dᴴ * D)))
      = ∑ g : Polynomial params,
          avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
              ev strategy.state (Dᴴ * D)) := by
          refine Finset.sum_congr rfl ?_
          intro g _
          apply avgOver_congr
          intro qu
          exact ev_adjoint_sub_swap strategy.state
            (weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
            (weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2)
    _ ≤ 2 * eps :=
        axisParallelPointLineConsistency_weighted_leftToRightLineQuestion_sum
          params strategy eps delta gamma hgood G

end MIPStarRE.LDT.GlobalVariance
