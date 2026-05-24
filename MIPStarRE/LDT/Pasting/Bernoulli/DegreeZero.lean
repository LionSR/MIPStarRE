import MIPStarRE.LDT.Pasting.Bernoulli.ScalarBounds
import MIPStarRE.LDT.Pasting.BridgeLemmas.HAConsistency

/-!
# Section 12 pasting: degree-zero branch

Auxiliary constructions for the `d = 0` complementary branch of
`thm:ld-pasting`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The degree-zero appended-slice candidate has the same total operator as the
averaged slice submeasurement. -/
private theorem averagedSliceAppendedSubMeas_total
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (averagedSliceAppendedSubMeas params family).total =
      family.averagedSubMeas.total := by
  rw [averagedSliceAppendedSubMeas, postprocess_total]

/-- Evaluating the degree-zero appended-slice candidate is the height average of
the original evaluated slice family at the same old point. -/
private theorem polynomialEvaluation_averagedSliceAppendedSubMeas_eq_average
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (u : Point params.next) :
    polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family) u =
      averageIdxSubMeas (uniformDistribution (Fq params))
        (fun x =>
          family.evaluatedAtNextPoint
            (appendPoint params (truncatePoint params u) x))
        (uniformDistribution_weight_sum_le_one (Fq params)) := by
  calc
    polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family) u
        = evaluateAt params.next u (averagedSliceAppendedSubMeas params family) := rfl
    _ = evaluateAt params (truncatePoint params u) family.averagedSubMeas := by
        exact evaluateAt_averagedSliceAppendedSubMeas params family u
    _ = averageIdxSubMeas (uniformDistribution (Fq params))
          (fun x => evaluateAt params (truncatePoint params u)
            ((family.meas x).toSubMeas))
          (uniformDistribution_weight_sum_le_one (Fq params)) := by
        exact evaluateAt_averageIdxSubMeas params (truncatePoint params u)
          (uniformDistribution (Fq params))
          (fun x => (family.meas x).toSubMeas)
          (uniformDistribution_weight_sum_le_one (Fq params))
    _ = averageIdxSubMeas (uniformDistribution (Fq params))
          (fun x =>
            family.evaluatedAtNextPoint
              (appendPoint params (truncatePoint params u) x))
          (uniformDistribution_weight_sum_le_one (Fq params)) := by
        congr
        funext x
        simp [IdxPolyFamily.evaluatedAtNextPoint, truncatePoint_appendPoint,
          pointHeight_appendPoint]

/-- The point-consistency hypothesis may be truncated at the trivial unit bound. -/
private theorem consistentWithPoints_min_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (zeta : Error)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    family.ConsistentWithPoints strategy (min zeta 1) := by
  refine ⟨?_⟩
  refine ⟨?_⟩
  exact le_min hcons.pointConsistency.offDiagonalBound
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint)

/-- Scalar absorption for the degree-zero submeasurement consistency error. -/
private theorem degreeZero_submeas_error_le_two_nu
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error) (k : ℕ)
    (hk_pos : 1 ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    min zeta 1 +
        2 * Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) ≤
      2 * MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
  let C : Error := ((k : Error) ^ (2 : ℕ)) * (params.m : Error)
  let epsTerm : Error := Real.rpow eps (1 / (32 : Error))
  let deltaTerm : Error := Real.rpow delta (1 / (32 : Error))
  let gammaTerm : Error := Real.rpow gamma (1 / (32 : Error))
  let zetaTerm : Error := Real.rpow zeta (1 / (32 : Error))
  let degreeTerm : Error :=
    Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
  let S : Error := epsTerm + deltaTerm + gammaTerm + zetaTerm + degreeTerm
  have hC_one : (1 : Error) ≤ C := by
    have hkE_one : (1 : Error) ≤ (k : Error) := by exact_mod_cast hk_pos
    have hmE_one : (1 : Error) ≤ (params.m : Error) := by
      exact_mod_cast (Nat.succ_le_of_lt params.hm)
    dsimp [C]
    nlinarith [sq_nonneg (k : Error)]
  have hC_nonneg : 0 ≤ C := le_trans zero_le_one hC_one
  have hepsTerm_nonneg : 0 ≤ epsTerm := by
    dsimp [epsTerm]
    exact Real.rpow_nonneg heps_nonneg _
  have hdeltaTerm_nonneg : 0 ≤ deltaTerm := by
    dsimp [deltaTerm]
    exact Real.rpow_nonneg hdelta_nonneg _
  have hgammaTerm_nonneg : 0 ≤ gammaTerm := by
    dsimp [gammaTerm]
    exact Real.rpow_nonneg hgamma_nonneg _
  have hzetaTerm_nonneg : 0 ≤ zetaTerm := by
    dsimp [zetaTerm]
    exact Real.rpow_nonneg hzeta_nonneg _
  have hdegreeTerm_nonneg : 0 ≤ degreeTerm := by
    dsimp [degreeTerm]
    exact Real.rpow_nonneg (ldPasting_degreeRatio_nonneg params) _
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    nlinarith
  have hzeta_min_le_C : min zeta 1 ≤ C * zetaTerm := by
    have hmin_nonneg : 0 ≤ min zeta 1 := by positivity
    have hmin_le_one : min zeta 1 ≤ 1 := min_le_right _ _
    have hzeta_min_le : min zeta 1 ≤ zetaTerm := by
      calc
        min zeta 1 ≤ Real.rpow (min zeta 1) (1 / (32 : Error)) := by
            simpa [Real.rpow_one] using
              (Real.rpow_le_rpow_of_exponent_ge' hmin_nonneg hmin_le_one
                (show 0 ≤ (1 / (32 : Error)) by norm_num)
                (show 1 / (32 : Error) ≤ (1 : Error) by norm_num))
        _ ≤ zetaTerm := by
            dsimp [zetaTerm]
            exact Real.rpow_le_rpow hmin_nonneg (min_le_left _ _) (by positivity)
    calc
      min zeta 1 ≤ zetaTerm := hzeta_min_le
      _ = (1 : Error) * zetaTerm := by ring
      _ ≤ C * zetaTerm := by
          exact mul_le_mul_of_nonneg_right hC_one hzetaTerm_nonneg
  have hsqrt_le_CS :
      Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) ≤ 3 * C * S := by
    calc
      Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
          ≤ 3 * ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
              (Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error))) :=
            hAConsistency_sqrt_bound_of_pos params eps delta k hk_pos
              heps_nonneg hdelta_nonneg
      _ = 3 * C * (epsTerm + deltaTerm) := by ring
      _ ≤ 3 * C * S := by
          have hsum_le : epsTerm + deltaTerm ≤ S := by
            dsimp [S]
            nlinarith
          exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
  calc
    min zeta 1 +
        2 * Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
      ≤ C * zetaTerm + 2 * (3 * C * S) := by
          exact add_le_add hzeta_min_le_C
            (mul_le_mul_of_nonneg_left hsqrt_le_CS (by norm_num))
    _ ≤ 7 * C * S := by
          have hzeta_le_S : zetaTerm ≤ S := by
            dsimp [S]
            nlinarith
          have hCzeta_le_CS : C * zetaTerm ≤ C * S := by
            exact mul_le_mul_of_nonneg_left hzeta_le_S hC_nonneg
          nlinarith
    _ ≤ 200 * C * S := by
          have hCS_nonneg : 0 ≤ C * S := mul_nonneg hC_nonneg hS_nonneg
          nlinarith
    _ = 2 * MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta := by
          simp [MainInductionStep.ldPastingInInductionNu, C, S, epsTerm, deltaTerm,
            gammaTerm, zetaTerm, degreeTerm]
          ring

/-- The averaged degree-zero pasted submeasurement is consistent with the lifted
vertical-line answers. -/
private theorem degreeZero_averagedSlice_liftedVerticalLineConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (liftedVerticalLineAnswerFamily params strategy)
      (min zeta 1 +
        Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)) := by
  let eps' : Error := min eps 1
  let delta' : Error := min delta 1
  let zeta' : Error := min zeta 1
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
  have hcons_small : family.ConsistentWithPoints strategy zeta' := by
    simpa [zeta'] using consistentWithPoints_min_one params strategy family zeta hcons
  have hgb := ldGbcon_liftedVerticalLine params strategy eps' delta' gamma zeta'
    hgood_small family hcons_small
  let F : Point params → Fq params → Error := fun u x =>
    qBipartiteConsDefect strategy.state
      (family.evaluatedAtNextPoint (appendPoint params u x))
      (liftedVerticalLineAnswerFamily params strategy (appendPoint params u x))
  have haverage_to_gb :
      avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params))
            (fun x => F (truncatePoint params u) x)) =
        bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          family.evaluatedAtNextPoint
          (liftedVerticalLineAnswerFamily params strategy) := by
    calc
      avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params))
            (fun x => F (truncatePoint params u) x))
        = avgOver (uniformDistribution (Fq params))
            (fun _ => avgOver (uniformDistribution (Point params))
              (fun u => avgOver (uniformDistribution (Fq params)) (fun x => F u x))) := by
            simpa [truncatePoint_appendPoint] using
              CommutativityPoints.avgOver_uniform_pointNext_decompose params
                (fun u => avgOver (uniformDistribution (Fq params))
                  (fun x => F (truncatePoint params u) x))
      _ = avgOver (uniformDistribution (Point params))
            (fun u => avgOver (uniformDistribution (Fq params)) (fun x => F u x)) := by
            simpa using avgOver_uniform_const (α := Fq params)
              (avgOver (uniformDistribution (Point params))
                (fun u => avgOver (uniformDistribution (Fq params)) (fun x => F u x)))
      _ = avgOver (uniformDistribution (Fq params))
            (fun x => avgOver (uniformDistribution (Point params)) (fun u => F u x)) := by
            exact avgOver_uniform_comm (fun u x => F u x)
      _ = avgOver (uniformDistribution (Point params.next))
            (fun v => F (truncatePoint params v) (pointHeight params v)) := by
            simpa [truncatePoint_appendPoint, pointHeight_appendPoint] using
              (CommutativityPoints.avgOver_uniform_pointNext_decompose params
                (fun v => F (truncatePoint params v) (pointHeight params v))).symm
      _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          family.evaluatedAtNextPoint
          (liftedVerticalLineAnswerFamily params strategy) := by
            unfold bipartiteConsError
            apply avgOver_congr
            intro v
            have happend :
                appendPoint params (truncatePoint params v) (pointHeight params v) = v := by
              exact (CommutativityPoints.pointNextEquiv params).left_inv v
            simp [F, happend]
  constructor
  unfold bipartiteConsError
  calc
    avgOver (uniformDistribution (Point params.next))
        (fun u => qBipartiteConsDefect strategy.state
          (polynomialEvaluationFamily params.next
            (averagedSliceAppendedSubMeas params family) u)
          (liftedVerticalLineAnswerFamily params strategy u))
      ≤ avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params)) (fun x =>
            qBipartiteConsDefect strategy.state
              (family.evaluatedAtNextPoint (appendPoint params (truncatePoint params u) x))
              (liftedVerticalLineAnswerFamily params strategy u))) := by
          apply avgOver_mono
          intro u
          simpa [polynomialEvaluation_averagedSliceAppendedSubMeas_eq_average params family u] using
            qBipartiteConsDefect_averageIdxSubMeas_left_le strategy.state
              (uniformDistribution (Fq params))
              (fun x => family.evaluatedAtNextPoint
                (appendPoint params (truncatePoint params u) x))
              (liftedVerticalLineAnswerFamily params strategy u)
              (uniformDistribution_weight_sum_le_one (Fq params))
    _ = avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params))
            (fun x => F (truncatePoint params u) x)) := by
          apply avgOver_congr
          intro u
          apply avgOver_congr
          intro x
          have hline :
              liftedVerticalLineAnswerFamily params strategy
                  (appendPoint params (truncatePoint params u) x) =
                liftedVerticalLineAnswerFamily params strategy u := by
            exact liftedVerticalLineAnswerFamily_eq_of_same_truncate_degree_zero
              params strategy hd_zero (by simp)
          simp [F, hline]
    _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          family.evaluatedAtNextPoint
          (liftedVerticalLineAnswerFamily params strategy) := haverage_to_gb
    _ ≤ zeta' + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta') :=
          hgb.offDiagonalBound
    _ = min zeta 1 +
        Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) := by
          simp [eps', delta', zeta']

/-- The averaged degree-zero pasted submeasurement is point-consistent before
completion. -/
private theorem degreeZero_averagedSlice_pointConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (min zeta 1 +
        2 * Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)) := by
  let eps' : Error := min eps 1
  let delta' : Error := min delta 1
  let lineMeas : IdxMeas (Point params.next) (Fq params) ι := fun u =>
    { toSubMeas := liftedVerticalLineAnswerFamily params strategy u
      total_eq_one := by
        let ℓ : AxisParallelLine params.next :=
          { base := appendPoint params (truncatePoint params u) zeroCoord
            direction := lastCoord params }
        simpa [liftedVerticalLineAnswerFamily, verticalLineMeasurementFamily, ℓ,
          postprocess_total] using (strategy.axisParallelMeasurement ℓ).total_eq_one }
  let pointMeas : IdxMeas (Point params.next) (Fq params) ι :=
    fun u => (strategy.pointMeasurement u).toMeasurement
  have hline :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next
          (averagedSliceAppendedSubMeas params family))
        (IdxMeas.toIdxSubMeas lineMeas)
        (min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    simpa [lineMeas, eps', delta'] using
      degreeZero_averagedSlice_liftedVerticalLineConsistency params strategy
        eps delta gamma zeta hgood family hcons hd_zero
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
  have hpoint_sdd :
      SDDRel strategy.state (uniformDistribution (Point params.next))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas lineMeas))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas))
        (8 * (params.m : Error) * eps' + 4 * delta') := by
    refine Preliminaries.sddRel_symm strategy.state
      (uniformDistribution (Point params.next)) _ _ _ ?_
    simpa [lineMeas, pointMeas, liftedVerticalLineAnswerFamily] using
      pointVerticalLineSdd params strategy eps' delta' gamma hgood_small
  have htri :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next
          (averagedSliceAppendedSubMeas params family))
        (IdxMeas.toIdxSubMeas pointMeas)
        ((min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) +
          Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    exact Preliminaries.triangleSub_right strategy.state
      (uniformDistribution (Point params.next))
      strategy.isNormalized
      (by simpa using uniformDistribution_weight_sum_le_one (Point params.next))
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      lineMeas pointMeas
      (min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta'))
      (8 * (params.m : Error) * eps' + 4 * delta')
      hline hpoint_sdd
  have hswap :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (averagedSliceAppendedSubMeas params family))
        ((min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) +
          Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (IdxMeas.toIdxSubMeas pointMeas)
      ((min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) +
        Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta'))
      htri
  exact ConsRel.mono (by
    simp [eps', delta']
    ring_nf
    exact le_rfl) hswap

/-- Axis/self-consistency form of the degree-zero lifted-line consistency
estimate.

The degree-zero averaging argument uses the axis-parallel test and
self-consistency, but not the diagonal-line test. -/
private theorem degreeZero_averagedSlice_liftedVerticalLineConsistency_of_axis_self
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (liftedVerticalLineAnswerFamily params strategy)
      (min zeta 1 +
        Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)) := by
  let eps' : Error := min eps 1
  let delta' : Error := min delta 1
  let zeta' : Error := min zeta 1
  have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
    simpa [SymStrat.axisParallelFailureProbability] using
      bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
  have hself_le_one : strategy.selfConsistencyFailureProbability ≤ 1 := by
    simpa [SymStrat.selfConsistencyFailureProbability] using
      bipartiteSSCError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
  have haxis_small : strategy.axisParallelFailureProbability ≤ eps' := by
    exact le_min haxis haxis_le_one
  have hself_small : strategy.selfConsistencyFailureProbability ≤ delta' := by
    exact le_min hself hself_le_one
  have hcons_small : family.ConsistentWithPoints strategy zeta' := by
    simpa [zeta'] using consistentWithPoints_min_one params strategy family zeta hcons
  have hgb := ldGbcon_liftedVerticalLine_of_axis_self params strategy eps' delta' zeta'
    haxis_small hself_small family hcons_small
  let F : Point params → Fq params → Error := fun u x =>
    qBipartiteConsDefect strategy.state
      (family.evaluatedAtNextPoint (appendPoint params u x))
      (liftedVerticalLineAnswerFamily params strategy (appendPoint params u x))
  have haverage_to_gb :
      avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params))
            (fun x => F (truncatePoint params u) x)) =
        bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          family.evaluatedAtNextPoint
          (liftedVerticalLineAnswerFamily params strategy) := by
    calc
      avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params))
            (fun x => F (truncatePoint params u) x))
        = avgOver (uniformDistribution (Fq params))
            (fun _ => avgOver (uniformDistribution (Point params))
              (fun u => avgOver (uniformDistribution (Fq params)) (fun x => F u x))) := by
            simpa [truncatePoint_appendPoint] using
              CommutativityPoints.avgOver_uniform_pointNext_decompose params
                (fun u => avgOver (uniformDistribution (Fq params))
                  (fun x => F (truncatePoint params u) x))
      _ = avgOver (uniformDistribution (Point params))
            (fun u => avgOver (uniformDistribution (Fq params)) (fun x => F u x)) := by
            simpa using avgOver_uniform_const (α := Fq params)
              (avgOver (uniformDistribution (Point params))
                (fun u => avgOver (uniformDistribution (Fq params)) (fun x => F u x)))
      _ = avgOver (uniformDistribution (Fq params))
            (fun x => avgOver (uniformDistribution (Point params)) (fun u => F u x)) := by
            exact avgOver_uniform_comm (fun u x => F u x)
      _ = avgOver (uniformDistribution (Point params.next))
            (fun v => F (truncatePoint params v) (pointHeight params v)) := by
            simpa [truncatePoint_appendPoint, pointHeight_appendPoint] using
              (CommutativityPoints.avgOver_uniform_pointNext_decompose params
                (fun v => F (truncatePoint params v) (pointHeight params v))).symm
      _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          family.evaluatedAtNextPoint
          (liftedVerticalLineAnswerFamily params strategy) := by
            unfold bipartiteConsError
            apply avgOver_congr
            intro v
            have happend :
                appendPoint params (truncatePoint params v) (pointHeight params v) = v := by
              exact (CommutativityPoints.pointNextEquiv params).left_inv v
            simp [F, happend]
  constructor
  unfold bipartiteConsError
  calc
    avgOver (uniformDistribution (Point params.next))
        (fun u => qBipartiteConsDefect strategy.state
          (polynomialEvaluationFamily params.next
            (averagedSliceAppendedSubMeas params family) u)
          (liftedVerticalLineAnswerFamily params strategy u))
      ≤ avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params)) (fun x =>
            qBipartiteConsDefect strategy.state
              (family.evaluatedAtNextPoint (appendPoint params (truncatePoint params u) x))
              (liftedVerticalLineAnswerFamily params strategy u))) := by
          apply avgOver_mono
          intro u
          simpa [polynomialEvaluation_averagedSliceAppendedSubMeas_eq_average params family u] using
            qBipartiteConsDefect_averageIdxSubMeas_left_le strategy.state
              (uniformDistribution (Fq params))
              (fun x => family.evaluatedAtNextPoint
                (appendPoint params (truncatePoint params u) x))
              (liftedVerticalLineAnswerFamily params strategy u)
              (uniformDistribution_weight_sum_le_one (Fq params))
    _ = avgOver (uniformDistribution (Point params.next))
          (fun u => avgOver (uniformDistribution (Fq params))
            (fun x => F (truncatePoint params u) x)) := by
          apply avgOver_congr
          intro u
          apply avgOver_congr
          intro x
          have hline :
              liftedVerticalLineAnswerFamily params strategy
                  (appendPoint params (truncatePoint params u) x) =
                liftedVerticalLineAnswerFamily params strategy u := by
            exact liftedVerticalLineAnswerFamily_eq_of_same_truncate_degree_zero
              params strategy hd_zero (by simp)
          simp [F, hline]
    _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          family.evaluatedAtNextPoint
          (liftedVerticalLineAnswerFamily params strategy) := haverage_to_gb
    _ ≤ zeta' + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta') :=
          hgb.offDiagonalBound
    _ = min zeta 1 +
        Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) := by
          simp [eps', delta', zeta']

/-- Axis/self-consistency form of the degree-zero point-consistency estimate
before completion. -/
private theorem degreeZero_averagedSlice_pointConsistency_of_axis_self
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (min zeta 1 +
        2 * Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)) := by
  let eps' : Error := min eps 1
  let delta' : Error := min delta 1
  let lineMeas : IdxMeas (Point params.next) (Fq params) ι := fun u =>
    { toSubMeas := liftedVerticalLineAnswerFamily params strategy u
      total_eq_one := by
        let ℓ : AxisParallelLine params.next :=
          { base := appendPoint params (truncatePoint params u) zeroCoord
            direction := lastCoord params }
        simpa [liftedVerticalLineAnswerFamily, verticalLineMeasurementFamily, ℓ,
          postprocess_total] using (strategy.axisParallelMeasurement ℓ).total_eq_one }
  let pointMeas : IdxMeas (Point params.next) (Fq params) ι :=
    fun u => (strategy.pointMeasurement u).toMeasurement
  have hline :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next
          (averagedSliceAppendedSubMeas params family))
        (IdxMeas.toIdxSubMeas lineMeas)
        (min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    simpa [lineMeas, eps', delta'] using
      degreeZero_averagedSlice_liftedVerticalLineConsistency_of_axis_self params strategy
        eps delta zeta haxis hself family hcons hd_zero
  have haxis_le_one : strategy.axisParallelFailureProbability ≤ 1 := by
    simpa [SymStrat.axisParallelFailureProbability] using
      bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (axisParallelPointAnswerFamily strategy)
        (axisParallelLineAnswerFamily strategy)
  have hself_le_one : strategy.selfConsistencyFailureProbability ≤ 1 := by
    simpa [SymStrat.selfConsistencyFailureProbability] using
      bipartiteSSCError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
  have haxis_small : strategy.axisParallelFailureProbability ≤ eps' := by
    exact le_min haxis haxis_le_one
  have hself_small : strategy.selfConsistencyFailureProbability ≤ delta' := by
    exact le_min hself hself_le_one
  have hpoint_sdd :
      SDDRel strategy.state (uniformDistribution (Point params.next))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas lineMeas))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas pointMeas))
        (8 * (params.m : Error) * eps' + 4 * delta') := by
    refine Preliminaries.sddRel_symm strategy.state
      (uniformDistribution (Point params.next)) _ _ _ ?_
    simpa [lineMeas, pointMeas, liftedVerticalLineAnswerFamily] using
      pointVerticalLineSdd_of_axis_self params strategy eps' delta'
        haxis_small hself_small
  have htri :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (polynomialEvaluationFamily params.next
          (averagedSliceAppendedSubMeas params family))
        (IdxMeas.toIdxSubMeas pointMeas)
        ((min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) +
          Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    exact Preliminaries.triangleSub_right strategy.state
      (uniformDistribution (Point params.next))
      strategy.isNormalized
      (by simpa using uniformDistribution_weight_sum_le_one (Point params.next))
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      lineMeas pointMeas
      (min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta'))
      (8 * (params.m : Error) * eps' + 4 * delta')
      hline hpoint_sdd
  have hswap :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (averagedSliceAppendedSubMeas params family))
        ((min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) +
          Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) := by
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (IdxMeas.toIdxSubMeas pointMeas)
      ((min zeta 1 + Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta')) +
        Real.sqrt (8 * (params.m : Error) * eps' + 4 * delta'))
      htri
  exact ConsRel.mono (by
    simp [eps', delta']
    ring_nf
    exact le_rfl) hswap

/-- Degree-zero point-consistency construction for `thm:ld-pasting`.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  In the degree-zero
branch the slice polynomials and the last-coordinate line answers are constant
on their respective domains.  The measurement is the completion of
`averagedSliceAppendedSubMeas`, the averaged slice family viewed as a global
polynomial family by ignoring the appended variable. -/
theorem degreeZeroPastedPointConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0)
    (k : ℕ) :
    ∃ H : Measurement (Polynomial params.next) ι,
      H =
          Preliminaries.completeAtOutcome
            (averagedSliceAppendedSubMeas params family)
            (pastedFallbackOutcome params) ∧
        ConsRel strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params.next H.toSubMeas)
          (MainInductionStep.ldPastingInInductionError params k
            eps delta gamma kappa zeta) := by
  let S : SubMeas (Polynomial params.next) ι := averagedSliceAppendedSubMeas params family
  let H : Measurement (Polynomial params.next) ι :=
    Preliminaries.completeAtOutcome S (pastedFallbackOutcome params)
  refine ⟨H, rfl, ?_⟩
  by_cases hk_pos : 1 ≤ k
  · let η : Error := min zeta 1 +
      2 * Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
    let ν : Error := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
    have hsubmeas :
        ConsRel strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params.next S) η := by
      simpa [S, η] using
        degreeZero_averagedSlice_pointConsistency params strategy eps delta gamma zeta
          hgood family hcons hd_zero
    let completedEval : IdxSubMeas (Point params.next) (Fq params) ι :=
      fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u S)
        ((pastedFallbackOutcome params) u)).toSubMeas
    have hcompletedEval :
        completedEval = polynomialEvaluationFamily params.next H.toSubMeas := by
      funext u
      simpa [completedEval, H, S, polynomialEvaluationFamily] using
        (Preliminaries.evaluateAt_completeAtOutcome params.next S
          (pastedFallbackOutcome params) u).symm
    have hresidualMass :
        ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total)) ≤ kappa := by
      have hmass : ev strategy.state (leftTensor (ι₂ := ι) S.total) ≥ 1 - kappa := by
        simpa [S, averagedSliceAppendedSubMeas, subMeasMass, SubMeas.liftLeft,
          postprocess_total] using hcomplete.averageCompleteness.lowerBound
      calc
        ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total))
          = ev strategy.state (leftTensor (ι₂ := ι) (1 - S.total)) := by
              simpa using (strategy.permInvState.swap_ev (1 - S.total)).symm
        _ = 1 - ev strategy.state (leftTensor (ι₂ := ι) S.total) := by
              have hleftSub :
                  leftTensor (ι₂ := ι) (1 - S.total) =
                    1 - leftTensor (ι₂ := ι) S.total := by
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
                  simp [leftTensor, h₁, h₂, sub_eq_add_neg]
              rw [hleftSub, ev_sub]
              simp [ev_one_of_isNormalized strategy.state strategy.isNormalized]
        _ ≤ kappa := by linarith
    have hcompleted :
        ConsRel strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          completedEval (η + kappa) := by
      constructor
      calc
        bipartiteConsError strategy.state (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            completedEval
          ≤ avgOver (uniformDistribution (Point params.next)) (fun u =>
              qBipartiteConsDefect strategy.state
                ((strategy.pointMeasurement u).toSubMeas)
                (evaluateAt params.next u S) +
              ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total))) := by
                unfold bipartiteConsError completedEval
                apply avgOver_mono
                intro u
                simpa [S, evaluateAt, postprocess_total] using
                  Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
                    strategy.state (strategy.pointMeasurement u).toMeasurement
                    (evaluateAt params.next u S)
                    ((pastedFallbackOutcome params) u)
        _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              (polynomialEvaluationFamily params.next S) +
            avgOver (uniformDistribution (Point params.next))
              (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total))) := by
                unfold bipartiteConsError
                rw [avgOver_add]
                simp [IdxProjMeas.toIdxSubMeas, polynomialEvaluationFamily]
        _ ≤ η + avgOver (uniformDistribution (Point params.next))
              (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total))) := by
                exact add_le_add hsubmeas.offDiagonalBound le_rfl
        _ = η + ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total)) := by
              simpa using avgOver_uniform_const (α := Point params.next)
                (ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total)))
        _ ≤ η + kappa := by linarith
    have heps_nonneg : 0 ≤ eps := eps_nonneg_of_isGood params.next strategy hgood
    have hdelta_nonneg : 0 ≤ delta := delta_nonneg_of_isGood params.next strategy hgood
    have hgamma_nonneg : 0 ≤ gamma := gamma_nonneg_of_isGood params.next strategy hgood
    have hzeta_nonneg : 0 ≤ zeta :=
      IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons
    have hkappa_nonneg : 0 ≤ kappa :=
      kappa_nonneg_of_complete params strategy family hcomplete
    have heta_le : η ≤ 2 * ν := by
      simpa [η, ν] using
        degreeZero_submeas_error_le_two_nu params eps delta gamma zeta k hk_pos
          heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
    have hkappa_le :
        kappa ≤ kappa * (1 + 1 / (100 * (params.m : Error))) := by
      have hcoef : (1 : Error) ≤ 1 + 1 / (100 * (params.m : Error)) := by
        have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
        have hden_pos : (0 : Error) < 100 * (params.m : Error) := by positivity
        have hfrac_nonneg : 0 ≤ (1 : Error) / (100 * (params.m : Error)) :=
          div_nonneg zero_le_one hden_pos.le
        linarith
      simpa [one_mul] using mul_le_mul_of_nonneg_left hcoef hkappa_nonneg
    have herror_absorb :
        η + kappa ≤ MainInductionStep.ldPastingInInductionError params k
          eps delta gamma kappa zeta := by
      have hexp_nonneg :
          0 ≤ Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) :=
        le_of_lt (Real.exp_pos _)
      change η + kappa ≤
        kappa * (1 + 1 / (100 * (params.m : Error))) + 2 * ν +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))
      nlinarith
    exact ConsRel.mono herror_absorb (by simpa [hcompletedEval] using hcompleted)
  · have hk_zero : k = 0 := by omega
    exact ConsRel.mono
      (one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
        (kappa_nonneg_of_complete params strategy family hcomplete) hk_zero)
      ⟨bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)⟩

/-- Axis/self-consistency form of the degree-zero point-consistency
construction.

This is the same construction as `degreeZeroPastedPointConsistency`, with the
ordinary good-strategy package replaced by the two estimates actually used in
the proof. -/
theorem degreeZeroPastedPointConsistency_of_axis_self
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hselfBound : strategy.selfConsistencyFailureProbability ≤ delta)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0)
    (k : ℕ) :
    ∃ H : Measurement (Polynomial params.next) ι,
      H =
          Preliminaries.completeAtOutcome
            (averagedSliceAppendedSubMeas params family)
            (pastedFallbackOutcome params) ∧
        ConsRel strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params.next H.toSubMeas)
          (MainInductionStep.ldPastingInInductionError params k
            eps delta gamma kappa zeta) := by
  let S : SubMeas (Polynomial params.next) ι := averagedSliceAppendedSubMeas params family
  let H : Measurement (Polynomial params.next) ι :=
    Preliminaries.completeAtOutcome S (pastedFallbackOutcome params)
  refine ⟨H, rfl, ?_⟩
  by_cases hk_pos : 1 ≤ k
  · let η : Error := min zeta 1 +
      2 * Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
    let ν : Error := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
    have hsubmeas :
        ConsRel strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params.next S) η := by
      simpa [S, η] using
        degreeZero_averagedSlice_pointConsistency_of_axis_self params strategy
          eps delta zeta haxis hselfBound family hcons hd_zero
    let completedEval : IdxSubMeas (Point params.next) (Fq params) ι :=
      fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u S)
        ((pastedFallbackOutcome params) u)).toSubMeas
    have hcompletedEval :
        completedEval = polynomialEvaluationFamily params.next H.toSubMeas := by
      funext u
      simpa [completedEval, H, S, polynomialEvaluationFamily] using
        (Preliminaries.evaluateAt_completeAtOutcome params.next S
          (pastedFallbackOutcome params) u).symm
    have hresidualMass :
        ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total)) ≤ kappa := by
      have hmass : ev strategy.state (leftTensor (ι₂ := ι) S.total) ≥ 1 - kappa := by
        simpa [S, averagedSliceAppendedSubMeas, subMeasMass, SubMeas.liftLeft,
          postprocess_total] using hcomplete.averageCompleteness.lowerBound
      calc
        ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total))
          = ev strategy.state (leftTensor (ι₂ := ι) (1 - S.total)) := by
              simpa using (strategy.permInvState.swap_ev (1 - S.total)).symm
        _ = 1 - ev strategy.state (leftTensor (ι₂ := ι) S.total) := by
              have hleftSub :
                  leftTensor (ι₂ := ι) (1 - S.total) =
                    1 - leftTensor (ι₂ := ι) S.total := by
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
                  simp [leftTensor, h₁, h₂, sub_eq_add_neg]
              rw [hleftSub, ev_sub]
              simp [ev_one_of_isNormalized strategy.state strategy.isNormalized]
        _ ≤ kappa := by linarith
    have hcompleted :
        ConsRel strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          completedEval (η + kappa) := by
      constructor
      calc
        bipartiteConsError strategy.state (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            completedEval
          ≤ avgOver (uniformDistribution (Point params.next)) (fun u =>
              qBipartiteConsDefect strategy.state
                ((strategy.pointMeasurement u).toSubMeas)
                (evaluateAt params.next u S) +
              ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total))) := by
                unfold bipartiteConsError completedEval
                apply avgOver_mono
                intro u
                simpa [S, evaluateAt, postprocess_total] using
                  Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
                    strategy.state (strategy.pointMeasurement u).toMeasurement
                    (evaluateAt params.next u S)
                    ((pastedFallbackOutcome params) u)
        _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
              (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
              (polynomialEvaluationFamily params.next S) +
            avgOver (uniformDistribution (Point params.next))
              (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total))) := by
                unfold bipartiteConsError
                rw [avgOver_add]
                simp [IdxProjMeas.toIdxSubMeas, polynomialEvaluationFamily]
        _ ≤ η + avgOver (uniformDistribution (Point params.next))
              (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total))) := by
                exact add_le_add hsubmeas.offDiagonalBound le_rfl
        _ = η + ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total)) := by
              simpa using avgOver_uniform_const (α := Point params.next)
                (ev strategy.state (rightTensor (ι₁ := ι) (1 - S.total)))
        _ ≤ η + kappa := by linarith
    have hzeta_nonneg : 0 ≤ zeta :=
      IdxPolyFamily.zeta_nonneg_of_consistentWithPoints strategy family hcons
    have hkappa_nonneg : 0 ≤ kappa :=
      kappa_nonneg_of_complete params strategy family hcomplete
    have heta_le : η ≤ 2 * ν := by
      simpa [η, ν] using
        degreeZero_submeas_error_le_two_nu params eps delta gamma zeta k hk_pos
          heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
    have hkappa_le :
        kappa ≤ kappa * (1 + 1 / (100 * (params.m : Error))) := by
      have hcoef : (1 : Error) ≤ 1 + 1 / (100 * (params.m : Error)) := by
        have hm_pos : (0 : Error) < (params.m : Error) := by exact_mod_cast params.hm
        have hden_pos : (0 : Error) < 100 * (params.m : Error) := by positivity
        have hfrac_nonneg : 0 ≤ (1 : Error) / (100 * (params.m : Error)) :=
          div_nonneg zero_le_one hden_pos.le
        linarith
      simpa [one_mul] using mul_le_mul_of_nonneg_left hcoef hkappa_nonneg
    have herror_absorb :
        η + kappa ≤ MainInductionStep.ldPastingInInductionError params k
          eps delta gamma kappa zeta := by
      have hexp_nonneg :
          0 ≤ Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) :=
        le_of_lt (Real.exp_pos _)
      change η + kappa ≤
        kappa * (1 + 1 / (100 * (params.m : Error))) + 2 * ν +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))
      nlinarith
    exact ConsRel.mono herror_absorb (by simpa [hcompletedEval] using hcompleted)
  · have hk_zero : k = 0 := by omega
    exact ConsRel.mono
      (one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
        (kappa_nonneg_of_complete params strategy family hcomplete) hk_zero)
      ⟨bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas)⟩

end MIPStarRE.LDT.Pasting
