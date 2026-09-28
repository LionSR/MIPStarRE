import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.LinearOrthogonalization
import MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair

/-!
# Linear rounding of consistent measurements

A consistency bound controls the idempotence defect of one complete
measurement on the corresponding marginal state.  The linear
orthogonalization lemma then gives the `18 ζ` distance bound.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `lem:orthonormalization-main-lemma` and
  `eq:consistent-measurement-orthogonalization`.
- `references/ldt-paper/orthonormalization.tex`,
  `lem:orthonormalization-main-lemma`, for the earlier weaker result.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective

/-- Consistent complete measurements admit a left-register projective rounding
at squared distance at most `18 ζ`. -/
theorem consistent_measurement_linear_bound {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB)
    (ζ : Error)
    (hCons : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ) :
    ∃ P : ProjMeas Outcome ιA,
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P.toSubMeas))
        (18 * ζ) := by
  classical
  rcases QuantumState.IsNormalized.nonempty (ι := ιA × ιB) hψ with ⟨⟨i, j⟩⟩
  letI : Nonempty ιA := ⟨i⟩
  letI : Nonempty ιB := ⟨j⟩
  let φ : QuantumState ιA := leftMarginalState ψ
  have hφ : φ.IsNormalized := leftMarginalState_isNormalized hψ
  have hAlmost := consistencyToAlmostProjective ψ A B ζ hCons
  have hsource :
      ∑ a, ev ψ
        ((leftLiftedMeasurement (ιB := ιB) A).outcome a -
          (leftLiftedMeasurement (ιB := ιB) A).outcome a *
            (leftLiftedMeasurement (ιB := ιB) A).outcome a) ≤ 2 * ζ := by
    simpa [consistencyToAlmostProjectiveError] using hAlmost.sourceAlmostProjective
  have hterm (a : Outcome) :
      ev ψ
        ((leftLiftedMeasurement (ιB := ιB) A).outcome a -
          (leftLiftedMeasurement (ιB := ιB) A).outcome a *
            (leftLiftedMeasurement (ιB := ιB) A).outcome a) =
      ev φ (A.outcome a - A.outcome a * A.outcome a) := by
    simpa [φ, leftLiftedMeasurement, leftPlacedSubMeas, leftTensor_sub,
      leftTensor_mul_leftTensor] using
      (leftMarginal_ev_eq (ψ := ψ) (X := A.outcome a - A.outcome a * A.outcome a))
  have hdefect : idempotenceDefect φ A ≤ 2 * ζ := by
    simpa [idempotenceDefect, hterm] using hsource
  obtain ⟨P, hP⟩ := exists_projective_measurement_linear_bound φ hφ A
  have hdist :
      (∑ a : Outcome,
        ev φ (((A.outcome a - P.outcome a)ᴴ) *
          (A.outcome a - P.outcome a))) ≤ 18 * ζ := by
    calc
      (∑ a : Outcome,
        ev φ (((A.outcome a - P.outcome a)ᴴ) *
          (A.outcome a - P.outcome a))) ≤
          9 * idempotenceDefect φ A := hP
      _ ≤ 9 * (2 * ζ) := by gcongr
      _ = 18 * ζ := by ring
  refine ⟨P, ?_⟩
  have hlift (a : Outcome) :
      ev ψ (((leftTensor (ι₂ := ιB) (A.outcome a) -
        leftTensor (ι₂ := ιB) (P.outcome a))ᴴ) *
        (leftTensor (ι₂ := ιB) (A.outcome a) -
          leftTensor (ι₂ := ιB) (P.outcome a))) =
      ev φ (((A.outcome a - P.outcome a)ᴴ) *
        (A.outcome a - P.outcome a)) := by
    simpa [φ, leftTensor_sub, leftTensor_conjTranspose,
      leftTensor_mul_leftTensor] using
      (leftMarginal_ev_eq (ψ := ψ)
        (X := (A.outcome a - P.outcome a)ᴴ *
          (A.outcome a - P.outcome a)))
  constructor
  have hq : qSDD ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
      (leftPlacedSubMeas (ιB := ιB) P.toSubMeas) ≤ 18 * ζ := by
    unfold qSDD qSDDCore
    simpa only [leftPlacedSubMeas_outcome] using
      (show (∑ a : Outcome,
        ev ψ (((leftTensor (ι₂ := ιB) (A.outcome a) -
          leftTensor (ι₂ := ιB) (P.outcome a))ᴴ) *
          (leftTensor (ι₂ := ιB) (A.outcome a) -
            leftTensor (ι₂ := ιB) (P.outcome a)))) ≤ 18 * ζ from by
        simpa only [hlift] using hdist)
  simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using hq

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
