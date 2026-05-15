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
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complete a source-facing pasting submeasurement once its point consistency
and mass lower bound have been proved.

This is the completion argument used in `cor:h-a-consistency`, specialized to
the final `thm:ld-pasting` error envelope.  It is independent of the particular
pasting construction and is used for the degree-zero candidate
`averagedSliceAppendedSubMeas`. -/
private theorem completeAtOutcome_pointConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (H : SubMeas (Polynomial params.next) ι)
    (hsubmeas :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H)
        (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta))
    (hcomplete :
      CompletenessAtLeast strategy.state H.liftLeft
        (ldPastingCompletenessLowerBound params kappa
          (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k)) :
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

/-- The degree-zero appended-slice candidate has the same total operator as the
averaged slice submeasurement. -/
private theorem averagedSliceAppendedSubMeas_total
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    (averagedSliceAppendedSubMeas params family).total =
      family.averagedSubMeas.total := by
  rw [averagedSliceAppendedSubMeas, postprocess_total]

/-- Completeness of the averaged slice family transfers to the degree-zero
appended-slice candidate. -/
private theorem averagedSliceAppendedSubMeas_completeness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hν_nonneg :
      0 ≤ MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) :
    CompletenessAtLeast strategy.state
      (averagedSliceAppendedSubMeas params family).liftLeft
      (ldPastingCompletenessLowerBound params kappa
        (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k) := by
  let ν := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  have hν_nonneg' : 0 ≤ ν := by simpa [ν] using hν_nonneg
  have hlower :
      ldPastingCompletenessLowerBound params kappa ν k ≤ 1 - kappa := by
    have hcoef_nonneg : 0 ≤ kappa * ((params.m : Error)⁻¹) * (1 / 100 : Error) := by
      have hkappa_nonneg : 0 ≤ kappa := kappa_nonneg_of_complete params strategy family hcomplete
      positivity
    have hexp_nonneg :
        0 ≤ Real.exp ((k : Error) * ((params.m : Error)⁻¹) ^ (2 : ℕ) * (-1 / 80000)) :=
      le_of_lt (Real.exp_pos _)
    simp [ldPastingCompletenessLowerBound]
    ring_nf
    nlinarith [hν_nonneg', hexp_nonneg, hcoef_nonneg]
  refine ⟨?_⟩
  calc
    ldPastingCompletenessLowerBound params kappa ν k
      ≤ 1 - kappa := hlower
    _ ≤ subMeasMass strategy.state family.averagedSubMeas.liftLeft :=
        hcomplete.averageCompleteness.lowerBound
    _ = subMeasMass strategy.state
          (averagedSliceAppendedSubMeas params family).liftLeft := by
        simp [subMeasMass, SubMeas.liftLeft, averagedSliceAppendedSubMeas_total params family]

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

/-- Degree-zero vertical-line consistency rectangle for `thm:ld-pasting`.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  This is the
remaining mathematical core of issue #1622 after the completion, mass transport,
and H-A point-consistency transport have been separated.  It should combine
`ldGbcon_liftedVerticalLine`, the two degree-zero invariance lemmas, and the
height-averaging identity
`polynomialEvaluation_averagedSliceAppendedSubMeas_eq_average`.

The statement has no bridge, residual, repair, producer, or package hypothesis. -/
theorem degreeZeroPastedLineConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0)
    (k : ℕ)
    (hk_pos : 1 ≤ k) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (hRestrictionToVerticalLine params
        (averagedSliceAppendedSubMeas params family))
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k) := by
  -- Issue #1622: prove the degree-zero height-averaging rectangle on vertical
  -- lines.  The proof should compare the averaged slice family with the lifted
  -- vertical-line answers using `ldGbcon_liftedVerticalLine` and the two
  -- degree-zero invariance lemmas, then absorb the resulting line error into
  -- `hBConsistencyError`.
  sorry

/-- Degree-zero submeasurement point consistency for `thm:ld-pasting`.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  This theorem is now
the formal H-A transport of `degreeZeroPastedLineConsistency`: once the
degree-zero candidate is consistent with the vertical-line measurements, the
standard point-to-vertical-line comparison for a good strategy gives the
ambient point-consistency statement.

The statement has no bridge, residual, repair, producer, or package hypothesis. -/
theorem degreeZeroPastedSubMeasPointConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hd_zero : params.d = 0)
    (k : ℕ)
    (hk_pos : 1 ≤ k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (averagedSliceAppendedSubMeas params family))
      (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) := by
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
  have hline :
      ConsRel strategy.state (uniformDistribution (Point params))
        (hRestrictionToVerticalLine params
          (averagedSliceAppendedSubMeas params family))
        (verticalLineMeasurementFamily params strategy)
        (hBConsistencyError params eps delta gamma zeta k) :=
    degreeZeroPastedLineConsistency params strategy eps delta gamma zeta
      hgood family hcons hd_zero k hk_pos
  exact hAConsistency_submeas_from_lineConsistency params strategy
    (averagedSliceAppendedSubMeas params family) eps delta gamma zeta
    hgood hgamma_nonneg hzeta_nonneg k hk_pos hline

/-- Degree-zero point-consistency construction for `thm:ld-pasting`.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  This is the
remaining source-faithful construction obligation for issue #1622.  In the
degree-zero branch the slice polynomials and the last-coordinate line answers
are constant on their respective domains.  The measurement is the completion of
`averagedSliceAppendedSubMeas`, the averaged slice family viewed as a global
polynomial family by ignoring the appended variable.

The statement deliberately has no bridge, residual, repair, producer, or
package hypothesis. -/
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
  let H : Measurement (Polynomial params.next) ι :=
    Preliminaries.completeAtOutcome
      (averagedSliceAppendedSubMeas params family)
      (pastedFallbackOutcome params)
  refine ⟨H, rfl, ?_⟩
  by_cases hk_zero : k = 0
  · exact ⟨le_trans
      (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next H.toSubMeas))
      (one_le_ldPastingError_of_k_eq_zero params k eps delta gamma kappa zeta
        (kappa_nonneg_of_complete params strategy family hcomplete) hk_zero)⟩
  · have hk_pos : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk_zero)
    have hsubmeas :
        ConsRel strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params.next
            (averagedSliceAppendedSubMeas params family))
          (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) :=
      degreeZeroPastedSubMeasPointConsistency params strategy eps delta gamma zeta
        hgood family hcons hd_zero k hk_pos
    have hν_nonneg :
        0 ≤ MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta :=
      le_trans
        (bipartiteConsError_nonneg strategy.state
          (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (polynomialEvaluationFamily params.next
            (averagedSliceAppendedSubMeas params family)))
        hsubmeas.offDiagonalBound
    have hcomplete_appended :
        CompletenessAtLeast strategy.state
          (averagedSliceAppendedSubMeas params family).liftLeft
          (ldPastingCompletenessLowerBound params kappa
            (MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta) k) :=
      averagedSliceAppendedSubMeas_completeness params strategy eps delta gamma
        kappa zeta family hcomplete k hν_nonneg
    simpa [H] using
      completeAtOutcome_pointConsistency params strategy eps delta gamma kappa zeta
        (averagedSliceAppendedSubMeas params family) hsubmeas hcomplete_appended

end MIPStarRE.LDT.Pasting
