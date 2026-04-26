import MIPStarRE.LDT.Commutativity.Main.Results
import MIPStarRE.LDT.Pasting.BridgeLemmas.HBConsistency

/-!
# Section 12 pasting: H-A consistency

Vertical-line to point-consistency bridge and completed-measurement wrapper for `cor:h-a-consistency`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Transport the vertical-line consistency statement from restricted points
`u : Point params` to ambient points `appendPoint params u x`. -/
private lemma liftedVerticalLineConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (H : SubMeas (Polynomial params.next) ι)
    (η : Error)
    (hHB : ConsRel strategy.state
      (uniformDistribution (Point params))
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      η) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next H)
      (liftedVerticalLineAnswerFamily params strategy)
      η := by
  have hprod :=
    Preliminaries.consRel_uniform_prod_fst
      (α := Point params)
      (β := Fq params)
      (Outcome := AxisLinePolynomial params.next)
      (ιA := ι)
      (ιB := ι)
      strategy.state
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      η
      hHB
  have hpost :=
    Preliminaries.consRelDataProcessing_questionDependent
      strategy.state
      (uniformDistribution (Point params × Fq params))
      (fun ux => hRestrictionToVerticalLine params H ux.1)
      (fun ux => verticalLineMeasurementFamily params strategy ux.1)
      η
      (fun ux linePoly => linePoly ux.2)
      hprod
  have hleft :
      ∀ ux : Point params × Fq params,
        postprocess (hRestrictionToVerticalLine params H ux.1)
            (fun linePoly => linePoly ux.2) =
          polynomialEvaluationFamily params.next H (appendPoint params ux.1 ux.2) := by
    intro ux
    rcases ux with ⟨u, x⟩
    change postprocess (hRestrictionToVerticalLine params H u)
        (fun linePoly => linePoly x) =
      polynomialEvaluationFamily params.next H (appendPoint params u x)
    rw [hRestrictionToVerticalLine, SubMeas.postprocess_comp]
    have hpt' :
        ({ base := appendPoint params u zeroCoord,
           direction := lastCoord params } : AxisParallelLine params.next).pointAt x =
          appendPoint params u x := by
      simpa using verticalLine_pointAt_appendPoint params u x
    have hfun :
        (fun a : Polynomial params.next =>
          (Polynomial.restrictToAxisParallelLine params.next a
              { base := appendPoint params u zeroCoord,
                direction := lastCoord params }).toFun x) =
          (fun a : Polynomial params.next => a (appendPoint params u x)) := by
      funext a
      change
        (Polynomial.restrictToAxisParallelLine params.next a
          { base := appendPoint params u zeroCoord,
            direction := lastCoord params }) x =
          a (appendPoint params u x)
      rw [Polynomial.restrictToAxisParallelLine_apply]
      rw [hpt']
    change postprocess H
      (fun a : Polynomial params.next =>
        (Polynomial.restrictToAxisParallelLine params.next a
            { base := appendPoint params u zeroCoord,
              direction := lastCoord params }).toFun x) = _
    rw [hfun]
    rfl
  have hright :
      ∀ ux : Point params × Fq params,
        postprocess (verticalLineMeasurementFamily params strategy ux.1)
            (fun linePoly => linePoly ux.2) =
          liftedVerticalLineAnswerFamily params strategy
            (appendPoint params ux.1 ux.2) := by
    intro ux
    rcases ux with ⟨u, x⟩
    simp [liftedVerticalLineAnswerFamily, truncatePoint_appendPoint, pointHeight_appendPoint]
  have hprod_next :
      ConsRel strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux => polynomialEvaluationFamily params.next H (appendPoint params ux.1 ux.2))
        (fun ux => liftedVerticalLineAnswerFamily params strategy (appendPoint params ux.1 ux.2))
        η := by
    simpa [hleft, hright] using hpost
  exact
    (Preliminaries.consRel_uniform_equiv
      (e := CommutativityPoints.pointNextEquiv params)
      (ψ := strategy.state)
      (A := polynomialEvaluationFamily params.next H)
      (B := liftedVerticalLineAnswerFamily params strategy)
      (δ := η)).mpr (by simpa [CommutativityPoints.pointNextEquiv] using hprod_next)

/-- Bridge: convert vertical-line consistency to point consistency.

Given `hHB : HBConsistencyStatement` (the output of `hBConsistency`), derives
point consistency by restricting the vertical-line bound to individual points.

Paper reference: `cor:h-a-consistency` proof in `ld-pasting.tex`
lines 1098–1117.

Steps:
1. Restrict `hHB.lineConsistency` to a single point on the line
2. Apply `triangleSub` with the `A-B` consistency bound from `hgood`
3. Error bound: `ν₆ + √(8mε + 4δ) ≤ 47k²m(...) ≤ 100k²m(...)` -/
private lemma hAConsistency_submeas_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k)
    (hHB : HBConsistencyStatement params strategy family
        eps delta gamma zeta k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  let H := constructedPastedSubMeas params family k
  let pointLineMeas : IdxMeas (Point params.next) (Fq params.next) ι := fun u =>
    { toSubMeas :=
        postprocess
          (verticalLineMeasurementFamily params strategy (truncatePoint params u))
          (fun f => f (pointHeight params u))
      total_eq_one := by
        let ℓ : AxisParallelLine params.next :=
          { base := appendPoint params (truncatePoint params u) zeroCoord
            direction := lastCoord params }
        simpa [verticalLineMeasurementFamily, ℓ, postprocess_total] using
          (strategy.axisParallelMeasurement ℓ).total_eq_one }
  let pointMeas : IdxMeas (Point params.next) (Fq params.next) ι :=
    fun u => (strategy.pointMeasurement u).toMeasurement
  let νB := hBConsistencyError params eps delta gamma zeta k
  let ν := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  let eps' : Error := min eps 1
  let delta' : Error := min delta 1
  have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
    simpa [SymStrat.axisParallelFailureProbability] using
      bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
  have hself_le_one : strategy.selfConsistencyFailureProbability ≤ 1 := by
    simpa [SymStrat.selfConsistencyFailureProbability] using
      bipartiteSSCError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
  have hgood_small : strategy.IsGood eps' delta' gamma := by
    refine ⟨?_, ?_, hgood.diagonalLineTest⟩
    · exact le_min hgood.axisParallelTest haxis_le_one
    · exact le_min hgood.selfConsistencyTest hself_le_one
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params.next))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      hgood.axisParallelTest
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (bipartiteSSCError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hgood.selfConsistencyTest
  have hline_prod :
      ConsRel strategy.state (uniformDistribution (VerticalLineQuestion params × Fq params))
        (fun ux => hRestrictionToVerticalLine params H ux.1)
        (fun ux => verticalLineMeasurementFamily params strategy ux.1)
        νB := by
    exact consRel_uniform_fst strategy.state
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      νB
      hHB.lineConsistency
  have hline_next :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (fun u => hRestrictionToVerticalLine params H (truncatePoint params u))
        (fun u => verticalLineMeasurementFamily params strategy (truncatePoint params u))
        νB := by
    exact (Preliminaries.consRel_uniform_equiv
      ((pointNextEquiv params).symm)
      strategy.state
      (fun ux => hRestrictionToVerticalLine params H ux.1)
      (fun ux => verticalLineMeasurementFamily params strategy ux.1)
      νB).1 hline_prod
  have hline_point :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next H)
        (IdxMeas.toIdxSubMeas pointLineMeas)
        νB := by
    have hproc :=
      Preliminaries.consRelDataProcessing_questionDependent strategy.state
        (uniformDistribution (Point params.next))
        (fun u => hRestrictionToVerticalLine params H (truncatePoint params u))
        (fun u => verticalLineMeasurementFamily params strategy (truncatePoint params u))
        νB
        (fun u f => f (pointHeight params u))
        hline_next
    simpa [pointLineMeas, polynomialEvaluationFamily,
      postprocess_hRestrictionToVerticalLine_eq_evaluateAt, H] using hproc
  have hpoint_sdd :
      SDDRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointLineMeas))
      (IdxSubMeas.liftRight (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
        (8 * (params.m : Error) * eps' + 4 * delta') := by
    exact Preliminaries.sddRel_symm strategy.state
      (uniformDistribution (Point params.next))
      _ _ _
      (by simpa [pointLineMeas, eps', delta'] using
        MIPStarRE.LDT.Pasting.pointVerticalLineSdd params strategy eps' delta' gamma hgood_small)
  have htri :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next H)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (νB + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    exact Preliminaries.triangleSub_right strategy.state
      (uniformDistribution (Point params.next))
      strategy.isNormalized
      (by simpa using uniformDistribution_weight_sum_le_one (Point params.next))
      (polynomialEvaluationFamily params.next H)
      pointLineMeas
      pointMeas
      νB
      (8 * (params.m : Error) * eps' + 4 * delta')
      hline_point
      hpoint_sdd
  have hswap :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H)
        (νB + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    exact bridge_consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next H)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (νB + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta'))
      htri
  refine ⟨?_⟩
  calc
    bipartiteConsError strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H)
      ≤ νB + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta') := hswap.offDiagonalBound
    _ ≤ ν := by
      exact hAConsistency_error_le_nu_of_pos params eps delta gamma zeta k hk_pos
        heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg

/-- `cor:h-a-consistency`.

This is the point-consistency part of the pasted-submeasurement chain.  The
completed-measurement consistency is deliberately separated as
`hAConsistency_completed`, since the paper proves it only after
`cor:ld-pasting-N-completeness`. -/
theorem hAConsistency_submeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  have hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
    have hfacts : GHatFactsStatement params strategy.state family gamma zeta := by
      have hzeta_nonneg : 0 ≤ zeta := by
        exact le_trans
          (bipartiteConsError_nonneg strategy.state
            (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            family.evaluatedAtNextPoint)
          hcons.pointConsistency.offDiagonalBound
      have hgamma_nonneg : 0 ≤ gamma := by
        have : 0 ≤ strategy.diagonalFailureProbability := by
          unfold SymStrat.diagonalFailureProbability
          exact mul_nonneg (by positivity)
            (Finset.sum_nonneg fun j _ => bipartiteConsError_nonneg strategy.state _ _ _)
        exact le_trans this hgood.diagonalLineTest
      let G : Fq params → SubMeas (Polynomial params) ι := fun x => (family.meas x).toSubMeas
      have hG : ∀ x, G x = (family.meas x).toSubMeas := by
        intro x
        rfl
      have hselfComplete :=
        gCompleteSelfConsistency params strategy.state family zeta
          strategy.permInvState hself
      have hselfIncomplete :=
        gBotSelfConsistency params strategy.state family zeta
          strategy.permInvState hselfComplete
      have hcomMain :=
        Commutativity.comMain params strategy eps delta gamma zeta
          strategy.isNormalized hgood family G hG hcons hself hbound
      have hcommComplete :=
        commutingWithGComplete params strategy family G gamma zeta
          hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hcomMain hselfComplete
      have hcommIncomplete :=
        commutingWithGIncomplete params strategy.state family gamma zeta hcommComplete
      exact gHatFacts params strategy.state family gamma zeta
        hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
        hselfComplete hselfIncomplete hcommComplete hcommIncomplete
    intro i hi
    exact ldSandwichLineOnePoint params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcons hself hbound hfacts k i hi
  have hHB := hBConsistency params strategy eps delta gamma zeta
    hgood hd family hcons hself hbound k hline
  have hgamma_nonneg : 0 ≤ gamma := by
    have : 0 ≤ strategy.diagonalFailureProbability := by
      unfold SymStrat.diagonalFailureProbability
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => bipartiteConsError_nonneg strategy.state _ _ _)
    exact le_trans this hgood.diagonalLineTest
  have hzeta_nonneg : 0 ≤ zeta := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        family.evaluatedAtNextPoint)
      hcons.pointConsistency.offDiagonalBound
  exact hAConsistency_submeas_core params strategy family
    eps delta gamma kappa zeta hgood hgamma_nonneg hzeta_nonneg hgamma_le hzeta_le hdq_le
    hcomplete k hk_pos hk hHB

/-- Completed-measurement version of `cor:h-a-consistency`.

This wrapper is intentionally downstream of `cor:ld-pasting-N-completeness`:
it may use the submeasurement consistency together with the completeness bound
for the constructed pasted submeasurement to control the added completion mass. -/
theorem hAConsistency_completed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (hsubmeas :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta))
    (hcomplete :
      CompletenessAtLeast strategy.state
        (constructedPastedSubMeas params family k).liftLeft
        (ldPastingCompletenessLowerBound params kappa
          (MainInductionStep.ldPastingInInductionNu params k
            eps delta gamma zeta) k)) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (constructedPastedMeasurement params family k).toSubMeas)
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta) := by
  let H := constructedPastedSubMeas params family k
  let ν := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  let completedEval : IdxSubMeas (Point params.next) (Fq params) ι :=
    fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u H)
      ((pastedFallbackOutcome params) u)).toSubMeas
  have hcompletedEval :
      completedEval =
        polynomialEvaluationFamily params.next
          (constructedPastedMeasurement params family k).toSubMeas := by
    funext u
    simpa [completedEval, H, constructedPastedMeasurement, pastedFallbackOutcome] using
      (Preliminaries.evaluateAt_completeAtOutcome params.next H
        (pastedFallbackOutcome params) u).symm
  have hresidualMass :
      ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)) ≤
        kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
    have hmass :
        ev strategy.state (leftTensor (ι₂ := ι) H.total) ≥
          ldPastingCompletenessLowerBound params kappa ν k := by
      simpa [H, subMeasMass, SubMeas.liftLeft] using hcomplete.lowerBound
    calc
      ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))
        = ev strategy.state (leftTensor (ι₂ := ι) (1 - H.total)) := by
            simpa using (strategy.permInvState.swap_ev (1 - H.total)).symm
      _ = 1 - ev strategy.state (leftTensor (ι₂ := ι) H.total) := by
            have hleftSub :
                leftTensor (ι₂ := ι) (1 - H.total) =
                  1 - leftTensor (ι₂ := ι) H.total := by
              ext i j
              rcases i with ⟨i₁, i₂⟩
              rcases j with ⟨j₁, j₂⟩
              by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
                simp [leftTensor, h₁, h₂, sub_eq_add_neg]
            rw [hleftSub, ev_sub]
            simp [ev_one_of_isNormalized strategy.state strategy.isNormalized]
      _ ≤ 1 - ldPastingCompletenessLowerBound params kappa ν k := by
            linarith
      _ = kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
            simp [ldPastingCompletenessLowerBound, ν]
            ring
  have hcompleted :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        completedEval
        (ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))) := by
    constructor
    calc
      bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          completedEval
        ≤ avgOver (uniformDistribution (Point params.next)) (fun u =>
            qBipartiteConsDefect strategy.state
                ((strategy.pointMeasurement u).toSubMeas)
                (evaluateAt params.next u H) +
              ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
                unfold bipartiteConsError completedEval
                apply avgOver_mono
                intro u
                simpa [H, evaluateAt, postprocess_total, ν] using
                  Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
                    strategy.state (strategy.pointMeasurement u).toMeasurement
                    (evaluateAt params.next u H)
                    ((pastedFallbackOutcome params) u)
      _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (polynomialEvaluationFamily params.next H) +
          avgOver (uniformDistribution (Point params.next))
            (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
              unfold bipartiteConsError
              rw [avgOver_add]
              simp [IdxProjMeas.toIdxSubMeas, polynomialEvaluationFamily]
      _ ≤ ν + avgOver (uniformDistribution (Point params.next))
            (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
              exact add_le_add hsubmeas.offDiagonalBound le_rfl
      _ = ν + ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)) := by
            simpa using avgOver_uniform_const (α := Point params.next)
              (ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)))
      _ ≤ ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
              gcongr
  have hsigma :
      ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
        Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) =
        MainInductionStep.ldPastingInInductionError params k
          eps delta gamma kappa zeta := by
    simp [MainInductionStep.ldPastingInInductionError, ν]
    ring
  exact ⟨by
    simpa [hcompletedEval] using le_trans hcompleted.offDiagonalBound hsigma.le⟩


end MIPStarRE.LDT.Pasting
