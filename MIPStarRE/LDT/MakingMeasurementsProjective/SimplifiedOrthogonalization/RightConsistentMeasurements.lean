import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.LinearOrthogonalization
import MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair

/-!
# Linear rounding on Bob's tensor factor

The right marginal converts the consistency estimate into an idempotence
defect for Bob's complete measurement.  The state-dependent orthogonalization
lemma gives the corresponding `18 ζ` bound on the right tensor factor.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `lem:orthonormalization-main-lemma`.
- `references/ldt-paper/orthonormalization.tex`,
  `lem:orthonormalization-main-lemma`.
- `references/ldt-paper/projectivization.tex`, for the right-register form.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective

/-- Consistent complete measurements admit a right-register projective rounding
at squared distance at most `18 ζ`. -/
theorem right_consistent_measurement_linear_bound {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB)
    (ζ : Error)
    (hCons : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ) :
    ∃ P : ProjMeas Outcome ιB,
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P.toSubMeas))
        (18 * ζ) := by
  classical
  rcases QuantumState.IsNormalized.nonempty (ι := ιA × ιB) hψ with ⟨⟨i, j⟩⟩
  letI : Nonempty ιA := ⟨i⟩
  letI : Nonempty ιB := ⟨j⟩
  let φ : QuantumState ιB := rightMarginalState ψ
  have hφ : φ.IsNormalized := rightMarginalState_isNormalized hψ
  have hAlmost := consistencyToAlmostProjective_right ψ A B ζ hCons
  have hsource :
      ∑ a, ev ψ
        ((rightLiftedMeasurement (ιA := ιA) B).outcome a -
          (rightLiftedMeasurement (ιA := ιA) B).outcome a *
            (rightLiftedMeasurement (ιA := ιA) B).outcome a) ≤ 2 * ζ := by
    simpa [consistencyToAlmostProjectiveError] using hAlmost.sourceAlmostProjective
  have hterm (a : Outcome) :
      ev ψ
        ((rightLiftedMeasurement (ιA := ιA) B).outcome a -
          (rightLiftedMeasurement (ιA := ιA) B).outcome a *
            (rightLiftedMeasurement (ιA := ιA) B).outcome a) =
      ev φ (B.outcome a - B.outcome a * B.outcome a) := by
    simpa [φ, rightLiftedMeasurement, rightPlacedSubMeas, rightTensor_sub,
      rightTensor_mul_rightTensor] using
      (rightMarginal_ev_eq (ψ := ψ) (X := B.outcome a - B.outcome a * B.outcome a))
  have hdefect : idempotenceDefect φ B ≤ 2 * ζ := by
    simpa [idempotenceDefect, hterm] using hsource
  obtain ⟨P, hP⟩ := exists_projective_measurement_linear_bound φ hφ B
  have hdist :
      (∑ a : Outcome,
        ev φ (((B.outcome a - P.outcome a)ᴴ) *
          (B.outcome a - P.outcome a))) ≤ 18 * ζ := by
    calc
      (∑ a : Outcome,
        ev φ (((B.outcome a - P.outcome a)ᴴ) *
          (B.outcome a - P.outcome a))) ≤
          9 * idempotenceDefect φ B := hP
      _ ≤ 9 * (2 * ζ) := by gcongr
      _ = 18 * ζ := by ring
  refine ⟨P, ?_⟩
  have hlift (a : Outcome) :
      ev ψ (((rightTensor (ι₁ := ιA) (B.outcome a) -
        rightTensor (ι₁ := ιA) (P.outcome a))ᴴ) *
        (rightTensor (ι₁ := ιA) (B.outcome a) -
          rightTensor (ι₁ := ιA) (P.outcome a))) =
      ev φ (((B.outcome a - P.outcome a)ᴴ) *
        (B.outcome a - P.outcome a)) := by
    simpa [φ, rightTensor_sub, rightTensor_conjTranspose,
      rightTensor_mul_rightTensor] using
      (rightMarginal_ev_eq (ψ := ψ)
        (X := (B.outcome a - P.outcome a)ᴴ *
          (B.outcome a - P.outcome a)))
  constructor
  have hq : qSDD ψ (rightPlacedSubMeas (ιA := ιA) B.toSubMeas)
      (rightPlacedSubMeas (ιA := ιA) P.toSubMeas) ≤ 18 * ζ := by
    unfold qSDD qSDDCore
    simpa only [rightPlacedSubMeas_outcome] using
      (show (∑ a : Outcome,
        ev ψ (((rightTensor (ι₁ := ιA) (B.outcome a) -
          rightTensor (ι₁ := ιA) (P.outcome a))ᴴ) *
          (rightTensor (ι₁ := ιA) (B.outcome a) -
            rightTensor (ι₁ := ιA) (P.outcome a)))) ≤ 18 * ζ from by
        simpa only [hlift] using hdist)
  simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using hq

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
