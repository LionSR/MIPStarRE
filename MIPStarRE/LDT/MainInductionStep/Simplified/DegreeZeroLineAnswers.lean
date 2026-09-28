import MIPStarRE.LDT.MainInductionStep.Simplified.DegreeZeroVariance

/-!
# Degree-zero axis-line answers along hypercube edges

When the line degree is zero, its answer is constant. Reparametrization
covariance therefore identifies the sampled answer at either endpoint
of a rerandomized-coordinate edge with one canonical line measurement.

## References

- `blueprint/src/low_degree_simplified.tex`, degree-zero proof of
  `thm:main-induction`.
- `references/ldt-paper/inductive_step.tex:441-551`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped BigOperators

universe uι

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

/-- The answer read from the canonical axis-parallel line through a point. -/
noncomputable def degreeZeroCanonicalAxisAnswer
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (u : Point params) (i : Fin params.m) : SubMeas (Fq params) ι :=
  postprocess
    (strategy.axisParallelMeasurement (AxisParallelLine.throughPoint u i)).toSubMeas
    (· zeroCoord)

/-- The line answer in the test agrees with the canonical line answer
when the degree bound is zero. -/
theorem degreeZero_axisAnswer_eq_canonical
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (hd : params.d = 0)
    (u : Point params) (i : Fin params.m) :
    AnswerSymStrat.axisParallelLineAnswerFamily strategy (u, i) =
      degreeZeroCanonicalAxisAnswer params strategy u i := by
  classical
  let ℓ := AxisParallelLine.throughPoint u i
  apply SubMeas.ext
  · intro a
    calc
      (AnswerSymStrat.axisParallelLineAnswerFamily strategy (u, i)).outcome a =
          (postprocess
            (strategy.axisParallelMeasurement ℓ).toSubMeas
            (fun f => f (u i))).outcome a := by
        have h := (AxisParallelCovariantMeasurement.reparamInvariant
          strategy.axisParallelMeasurement) ℓ (u i) a
        dsimp [ℓ] at h
        have hrebase :
            (AxisParallelLine.throughPoint u i).rebaseAt (u i) =
              ({ base := u, direction := i } : AxisParallelLine params) := by
          simpa [AxisParallelLine.sampleParameter] using
            (AxisParallelLine.rebaseAt_throughPoint_sampleParameter u i)
        rw [hrebase] at h
        simpa [AnswerSymStrat.axisParallelLineAnswerFamily,
          axisParallelLineAnswerFamilyOf, ℓ,
          AxisParallelLine.sampleParameter] using h
      _ = (degreeZeroCanonicalAxisAnswer params strategy u i).outcome a := by
        have hfun : (fun f : AxisLinePolynomial params => f (u i)) =
            (fun f => f zeroCoord) := by
          funext f
          exact AxisLinePolynomial.apply_eq_apply_of_degree_zero f hd _ _
        simp [degreeZeroCanonicalAxisAnswer, ℓ, hfun]
  · simpa [AnswerSymStrat.axisParallelLineAnswerFamily,
      axisParallelLineAnswerFamilyOf, degreeZeroCanonicalAxisAnswer,
      postprocess_total] using
      (strategy.axisParallelMeasurement
        { base := u, direction := i }).total_eq_one.trans
      (strategy.axisParallelMeasurement ℓ).total_eq_one.symm

/-- Replacing coordinate `i` leaves the canonical line unchanged. -/
theorem degreeZero_throughPoint_update
    (params : Parameters) [FieldModel params.q]
    (u : Point params) (i : Fin params.m) (t : Fq params) :
    AxisParallelLine.throughPoint (Function.update u i t) i =
      AxisParallelLine.throughPoint u i := by
  apply congrArg (fun b : Point params =>
    ({ base := b, direction := i } : AxisParallelLine params))
  funext j
  by_cases hj : j = i
  · simp [hj]
  · simp [hj]

/-- The test's degree-zero line-answer submeasurement is identical at
both endpoints of a rerandomized-coordinate edge. -/
theorem degreeZero_axisAnswer_update_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (hd : params.d = 0)
    (u : Point params) (i : Fin params.m) (t : Fq params) :
    AnswerSymStrat.axisParallelLineAnswerFamily strategy
        (Function.update u i t, i) =
      AnswerSymStrat.axisParallelLineAnswerFamily strategy (u, i) := by
  rw [degreeZero_axisAnswer_eq_canonical params strategy hd,
    degreeZero_axisAnswer_eq_canonical params strategy hd]
  simp [degreeZeroCanonicalAxisAnswer, degreeZero_throughPoint_update]

end MIPStarRE.LDT.MainInductionStep
