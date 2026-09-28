import MIPStarRE.LDT.Pasting.Simplified.ConsistencyAggregation
import MIPStarRE.LDT.Pasting.ComparisonLemmas.HAConsistency

/-!
# Point consistency for simplified pasting

The line-to-point transport from the existing proof applies to any
candidate polynomial submeasurement and any line consistency budget.
Keeping that budget explicit lets the sharper interpolation estimate
flow to the point consistency statement.

## References

- `blueprint/src/low_degree_simplified.tex`, `lem:pasting-consistency`.
- `references/ldt-paper/ld-pasting.tex`, `cor:h-a-consistency`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


/-- Transport a vertical-line consistency budget to point consistency,
adding the axis-parallel and point self-consistency distance. -/
theorem pointConsistency_of_verticalLineConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (H : SubMeas (Polynomial params.next) ι)
    (eps delta η : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (hline : ConsRel strategy.state
      (uniformDistribution (Point params))
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy) η) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next H)
      (η + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  let lineMeas : IdxMeas (Point params.next) (Fq params.next) ι := fun u =>
    { toSubMeas := liftedVerticalLineAnswerFamily params strategy u
      total_eq_one :=
        (strategy.axisParallelMeasurement
          { base := appendPoint params (truncatePoint params u) zeroCoord
            direction := lastCoord params }).total_eq_one }
  let pointMeas : IdxMeas (Point params.next) (Fq params.next) ι :=
    fun u => (strategy.pointMeasurement u).toMeasurement
  have hline_prod :
      ConsRel strategy.state
        (uniformDistribution (VerticalLineQuestion params × Fq params))
        (fun ux => hRestrictionToVerticalLine params H ux.1)
        (fun ux => verticalLineMeasurementFamily params strategy ux.1) η :=
    consRel_uniform_fst strategy.state
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy) η hline
  have hline_next :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (fun u => hRestrictionToVerticalLine params H (truncatePoint params u))
        (fun u => verticalLineMeasurementFamily params strategy
          (truncatePoint params u)) η := by
    exact (Preliminaries.consRel_uniform_equiv
      ((pointNextEquiv params).symm)
      strategy.state
      (fun ux => hRestrictionToVerticalLine params H ux.1)
      (fun ux => verticalLineMeasurementFamily params strategy ux.1)
      η).1 hline_prod
  have hline_point :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next H)
        (IdxMeas.toIdxSubMeas lineMeas) η := by
    have hproc :=
      Preliminaries.consRelDataProcessing_questionDependent strategy.state
        (uniformDistribution (Point params.next))
        (fun u => hRestrictionToVerticalLine params H (truncatePoint params u))
        (fun u => verticalLineMeasurementFamily params strategy
          (truncatePoint params u))
        η (fun u f => f (pointHeight params u)) hline_next
    have hleft :
        (fun u : Point params.next =>
          postprocess
            (hRestrictionToVerticalLine params H (truncatePoint params u))
            (fun f => f (pointHeight params u))) =
          (fun u => evaluateAt params.next u H) := by
      funext u
      exact postprocess_hRestrictionToVerticalLine_eq_evaluateAt params H u
    rw [hleft] at hproc
    change ConsRel strategy.state (uniformDistribution (Point params.next))
      (fun u => evaluateAt params.next u H)
      (fun u =>
        postprocess
          (verticalLineMeasurementFamily params strategy (truncatePoint params u))
          (fun f => f (pointHeight params u))) η
    exact hproc
  have hpoint_sdd :
      SDDRel strategy.state (uniformDistribution (Point params.next))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas lineMeas))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas))
        (8 * (params.m : Error) * eps + 4 * delta) := by
    have hpublic := pointVerticalLineSdd_liftedVerticalLine_of_axis_self
      params strategy eps delta haxis hself
    have hline_eq :
        IdxMeas.toIdxSubMeas lineMeas =
          liftedVerticalLineAnswerFamily params strategy := by
      funext u
      rfl
    have hpoint_eq :
        IdxMeas.toIdxSubMeas pointMeas =
          IdxProjMeas.toIdxSubMeas strategy.pointMeasurement := by
      funext u
      rfl
    rw [hline_eq, hpoint_eq]
    exact Preliminaries.sddRel_symm strategy.state
      (uniformDistribution (Point params.next)) _ _ _ hpublic
  have htri :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next H)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (η + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) :=
    Preliminaries.triangleSub_right strategy.state
      (uniformDistribution (Point params.next))
      strategy.isNormalized
      (by simpa using uniformDistribution_weight_sum_le_one (Point params.next))
      (polynomialEvaluationFamily params.next H)
      lineMeas pointMeas η
      (8 * (params.m : Error) * eps + 4 * delta)
      hline_point hpoint_sdd
  exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
    (uniformDistribution (Point params.next))
    (polynomialEvaluationFamily params.next H)
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (η + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) htri

/-- Point consistency of the distinct-success pasted submeasurement at
the simplified coarse rate. -/
theorem distinctSuccessPasted_pointConsistency_coarse
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself_good : strategy.selfConsistencyFailureProbability ≤ delta)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta_le_one : zeta ≤ 1)
    (hcom : Commutativity.ComMainConclusion params strategy family gamma zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hsc : SDDRel strategy.state (uniformDistribution (Fq params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (2 * zeta))
    (k : ℕ) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (distinctSuccessPastedSubMeas params family k))
      (2 * (k : Error) *
        (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
        2 * (k : Error) * ((k : Error) - 1) *
          (Real.sqrt (Commutativity.comMainError params gamma zeta) +
            4 * Real.sqrt zeta) +
        Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) := by
  apply pointConsistency_of_verticalLineConsistency params strategy
    (distinctSuccessPastedSubMeas params family k) eps delta
    (2 * (k : Error) *
      (zeta + Real.sqrt (8 * (params.m : Error) * eps + 4 * delta)) +
      2 * (k : Error) * ((k : Error) - 1) *
        (Real.sqrt (Commutativity.comMainError params gamma zeta) +
          4 * Real.sqrt zeta))
    haxis hself_good
  exact distinctSuccessPasted_verticalLine_consistency_coarse
    params strategy family eps delta gamma zeta
    haxis hself_good hcons strategy.isNormalized
    hzeta_nonneg hzeta_le_one hcom hself hsc k

end MIPStarRE.LDT.Pasting
