import MIPStarRE.LDT.GlobalVariance.Theorems.SelfConsistencyTransport.Point
import MIPStarRE.LDT.GlobalVariance.Theorems.SelfConsistencyTransport.PointLine

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
    axisParallelLineAnswerFamilyOf,
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
  simpa using
    cabApproxDelta_sum_from_sdd params strategy.state
      (uniformDistribution (AxisParallelTestSample params))
      (fun s => s.1)
      (fun s a => ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome a)
      (fun s a => ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome a)
      (fun s g =>
        let qu : AxisParallelLineQuestion params := ({ base := s.1, direction := s.2 }, s.1)
        weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu)
      (fun s g => weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1)
      G (2 * eps) hbase
      (by
        intro s g
        let qu : AxisParallelLineQuestion params := ({ base := s.1, direction := s.2 }, s.1)
        let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
        let L : MIPStarRE.Quantum.Op ι :=
          generalizeBLeftOperatorAtPolynomial params strategy g qu
        have hline_outcome :
            ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome (g s.1) =
              leftTensor (ι₂ := ι) L :=
          liftLeft_lineAnswerMeasurement_outcome_at_g params strategy g s
        change rightTensor (ι₁ := ι) S *
            ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas lineMeas)) s).outcome (g s.1) =
          weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
        rw [hline_outcome]
        change rightTensor (ι₁ := ι) S * leftTensor (ι₂ := ι) L = opTensor L S
        exact rightTensor_mul_leftTensor_eq_opTensor L S)
      (by
        intro s g
        let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
        let A : MIPStarRE.Quantum.Op ι :=
          pointConditionedOutcomeOperatorAtPolynomial params strategy g s.1
        have hpoint_outcome :
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome (g s.1) =
              rightTensor (ι₁ := ι) A :=
          liftRight_pointAnswerMeasurement_outcome_at_g params strategy g s
        change rightTensor (ι₁ := ι) S *
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas)) s).outcome (g s.1) =
          weightedPointConditionedRightOperatorAtPolynomial params strategy G g s.1
        rw [hpoint_outcome]
        change rightTensor (ι₁ := ι) S * rightTensor (ι₁ := ι) A =
          rightTensor (ι₁ := ι) (S * A)
        exact rightTensor_mul_rightTensor S A)

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
          have hrebase :
              weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (ℓ, ℓ.pointAt t) =
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (AxisParallelLine.rebaseAt ℓ t, ℓ.pointAt t) :=
            weightedGeneralizeBLeftOperatorAtPolynomial_rebaseAt_pointAt
              params strategy G g ℓ t
          rw [hrebase]
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
