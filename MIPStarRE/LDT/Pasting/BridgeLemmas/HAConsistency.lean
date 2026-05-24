import MIPStarRE.LDT.Commutativity.Main.Results
import MIPStarRE.LDT.Pasting.BridgeLemmas.HBConsistency
import MIPStarRE.LDT.Pasting.CommutingWithG.Complete
import MIPStarRE.LDT.Pasting.CommutingWithG.Incomplete

/-!
# Section 12 pasting: H-A consistency

Vertical-line to point-consistency transport and completed-measurement statement for
`cor:h-a-consistency`.

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

/-- Convert source-style vertical-line consistency to point consistency using only
the axis-parallel and self-consistency estimates.

This is the main estimate in `cor:h-a-consistency`, stated without the
intermediate `HBConsistencyStatement` type.  It takes only the line-consistency estimate
for a candidate polynomial submeasurement `H`, restricts that estimate to the
point on each vertical line, and then applies the good-strategy
point-to-vertical-line comparison.  The diagonal-line estimate in
`strategy.IsGood` is not used in this transport step; it enters earlier in the
construction of the line-consistency estimate.

Paper reference: `cor:h-a-consistency` proof in `ld-pasting.tex`
lines 1098–1117.

Steps:
1. Restrict the line-consistency hypothesis to a single point on the line
2. Apply `triangleSub` with the `A-B` consistency bound from `hgood`
3. Error bound: `ν₆ + √(8mε + 4δ) ≤ 47k²m(...) ≤ 100k²m(...)`.

The completion and large-`k` hypotheses are carried by the downstream
completed-measurement theorem; this submeasurement argument only uses the positive
`k` regime and the displayed line-consistency estimate. -/
theorem hAConsistency_submeas_from_lineConsistency_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (H : SubMeas (Polynomial params.next) ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hline :
      ConsRel strategy.state (uniformDistribution (Point params))
        (hRestrictionToVerticalLine params H)
        (verticalLineMeasurementFamily params strategy)
        (hBConsistencyError params eps delta gamma zeta k)) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H)
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
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
  have haxis_small : strategy.axisParallelFailureProbability ≤ eps' :=
    le_min haxis haxis_le_one
  have hself_small : strategy.selfConsistencyFailureProbability ≤ delta' :=
    le_min hself_good hself_le_one
  have heps_nonneg : 0 ≤ eps := by
    exact le_trans
      (bipartiteConsError_nonneg strategy.state
        (uniformDistribution (AxisParallelTestSample params.next))
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy))
      haxis
  have hdelta_nonneg : 0 ≤ delta := by
    exact le_trans
      (bipartiteSSCError_nonneg strategy.state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      hself_good
  have hline_prod :
      ConsRel strategy.state (uniformDistribution (VerticalLineQuestion params × Fq params))
        (fun ux => hRestrictionToVerticalLine params H ux.1)
        (fun ux => verticalLineMeasurementFamily params strategy ux.1)
        νB := by
    exact consRel_uniform_fst strategy.state
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      νB
      hline
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
      postprocess_hRestrictionToVerticalLine_eq_evaluateAt] using hproc
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
        (MIPStarRE.LDT.Pasting.pointVerticalLineSdd_of_axis_self
          params strategy eps' delta' haxis_small hself_small))
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
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
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

/-- Convert source-style vertical-line consistency to point consistency.

This source-style wrapper specializes
`hAConsistency_submeas_from_lineConsistency_of_axis_self` to the two estimates
contained in `strategy.IsGood`. -/
theorem hAConsistency_submeas_from_lineConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (H : SubMeas (Polynomial params.next) ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hline :
      ConsRel strategy.state (uniformDistribution (Point params))
        (hRestrictionToVerticalLine params H)
        (verticalLineMeasurementFamily params strategy)
        (hBConsistencyError params eps delta gamma zeta k)) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H)
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  exact hAConsistency_submeas_from_lineConsistency_of_axis_self params strategy H
    eps delta gamma zeta hgood.axisParallelTest hgood.selfConsistencyTest
    hgamma_nonneg hzeta_nonneg k hk_pos hline

/-- Specialization of `hAConsistency_submeas_from_lineConsistency` to the
constructed pasted submeasurement. -/
private lemma hAConsistency_submeas_core_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hHB : HBConsistencyStatement params strategy family
        eps delta gamma zeta k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
        (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  exact hAConsistency_submeas_from_lineConsistency_of_axis_self params strategy
    (constructedPastedSubMeas params family k) eps delta gamma zeta
    haxis hself_good hgamma_nonneg hzeta_nonneg k hk_pos hHB.lineConsistency

/-- Specialization of `hAConsistency_submeas_from_lineConsistency` to the
constructed pasted submeasurement. -/
private lemma hAConsistency_submeas_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hHB : HBConsistencyStatement params strategy family
        eps delta gamma zeta k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  exact hAConsistency_submeas_core_of_axis_self params strategy family
    eps delta gamma zeta hgood.axisParallelTest hgood.selfConsistencyTest
    hgamma_nonneg hzeta_nonneg k hk_pos hHB

/-- Internal form of `cor:h-a-consistency` from the one-point sandwich estimates.

This theorem separates the genuinely earlier pasting input from the diagonal
test.  Once the estimates of `lem:ld-sandwich-line-one-point` are known for all
positions, the passage from `H-B` consistency to `H-A` consistency uses only the
axis-parallel and self-consistency estimates of the ambient strategy. -/
theorem hAConsistency_submeas_ofLinePointBounds_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  have hHB := hBConsistency_ofLinePointBounds_of_axis_self params strategy
    eps delta gamma zeta haxis hself_good hgamma_nonneg hd
    family hcons hself hbound k hline
  exact hAConsistency_submeas_core_of_axis_self params strategy family
    eps delta gamma zeta haxis hself_good hgamma_nonneg hzeta_nonneg k hk_pos hHB

/-- Internal form of `cor:h-a-consistency` from `cor:G-hat-facts`.

This is the same proof as
`hAConsistency_submeas_ofLinePointBounds_of_axis_self`, with the one-point
sandwich estimates constructed from `GHatFactsStatement`. -/
theorem hAConsistency_submeas_ofGHatFacts_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  have hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
    intro i hi
    exact ldSandwichLineOnePoint_ofGHatFacts_of_axis_self params strategy
      eps delta gamma zeta haxis hself_good hgamma_nonneg hzeta_le
      family hcons hfacts k i hi
  exact hAConsistency_submeas_ofLinePointBounds_of_axis_self params strategy
    eps delta gamma zeta haxis hself_good hgamma_nonneg hzeta_nonneg hd
    family hcons hself hbound k hk_pos hline

/-- Internal form of `cor:h-a-consistency` from the Section 11 commutativity
conclusion.

This exposes the precise upstream mathematical input needed for the `G-hat`
construction.  The diagonal-line estimate is not used in the `H-B` to `H-A`
transport; it is used only insofar as it is needed to prove the commutativity
conclusion supplied here. -/
theorem hAConsistency_submeas_ofComMain_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  have hfacts : GHatFactsStatement params strategy.state family gamma zeta :=
    gHatFacts_ofComMainAndSelfConsistency params strategy family gamma zeta
      hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le hcom hself
  exact hAConsistency_submeas_ofGHatFacts_of_axis_self params strategy
    eps delta gamma zeta haxis hself_good hgamma_nonneg hzeta_nonneg
    hzeta_le hd family hcons hself hbound hfacts k hk_pos

/-- `cor:h-a-consistency`.

This is the point-consistency part of the pasted-submeasurement chain.  The
completed-measurement consistency is deliberately separated as
`hAConsistency_completed`, since the paper proves it only after
`cor:ld-pasting-N-completeness`. -/
theorem hAConsistency_submeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hd : 0 < params.d)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk_pos : 1 ≤ k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  have hHB := hBConsistency params strategy eps delta gamma zeta
    hgood hgamma_le hzeta_le hdq_le hd family hcons hself hbound k
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
    eps delta gamma zeta hgood hgamma_nonneg hzeta_nonneg k hk_pos hHB

/-- Complete a polynomial submeasurement after its point consistency and mass
lower bound have been proved.

This is the completion step in `cor:h-a-consistency`, stated for an arbitrary
submeasurement `H`.  The source argument first proves point consistency for a
submeasurement and then completes it by adding the missing mass to a fixed
fallback polynomial. -/
theorem hAConsistency_completed_from_submeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (H : SubMeas (Polynomial params.next) ι)
    (k : ℕ)
    (hsubmeas :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H)
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta))
    (hcomplete :
      CompletenessAtLeast strategy.state H.liftLeft
        (ldPastingCompletenessLowerBound params kappa
          (MainInductionStep.ldPastingInInductionNu params k
            eps delta gamma zeta) k)) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (Preliminaries.completeAtOutcome H (pastedFallbackOutcome params)).toSubMeas)
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta) := by
  let ν := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  let completedEval : IdxSubMeas (Point params.next) (Fq params) ι :=
    fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u H)
      ((pastedFallbackOutcome params) u)).toSubMeas
  have hcompletedEval :
      completedEval =
        polynomialEvaluationFamily params.next
          (Preliminaries.completeAtOutcome H (pastedFallbackOutcome params)).toSubMeas := by
    funext u
    simpa [completedEval, pastedFallbackOutcome] using
      (Preliminaries.evaluateAt_completeAtOutcome params.next H
        (pastedFallbackOutcome params) u).symm
  have hresidualMass :
      ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)) ≤
        kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
    have hmass :
        ev strategy.state (leftTensor (ι₂ := ι) H.total) ≥
          ldPastingCompletenessLowerBound params kappa ν k := by
      simpa [ν, subMeasMass, SubMeas.liftLeft] using hcomplete.lowerBound
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
                simpa [evaluateAt, postprocess_total, ν] using
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

/-- Completed-measurement version of `cor:h-a-consistency`.

This theorem is intentionally downstream of `cor:ld-pasting-N-completeness`:
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
  simpa [constructedPastedMeasurement] using
    hAConsistency_completed_from_submeas params strategy eps delta gamma kappa zeta
      (constructedPastedSubMeas params family k) k hsubmeas hcomplete

end MIPStarRE.LDT.Pasting
