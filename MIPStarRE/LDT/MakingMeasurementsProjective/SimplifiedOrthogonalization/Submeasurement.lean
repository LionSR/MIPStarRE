import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.LinearOrthogonalization
import MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.Completion
import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Local

/-!
# Linear rounding of symmetric submeasurements

A symmetric submeasurement is completed by a fresh failure outcome.  The
completed measurement has idempotence defect at most `2 ζ`; linear
orthogonalization and discarding the failure projector yield the `18 ζ`
bound.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `thm:orthonormalization` and
  `eq:strong-submeasurement-orthogonalization`.
- `references/ldt-paper/orthonormalization.tex`,
  `thm:orthonormalization`, for the earlier weaker bound.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective

/-- `thm:orthonormalization` in the simplified blueprint: a symmetric strongly
self-consistent submeasurement admits a projective submeasurement at squared
distance at most `18 ζ`. -/
theorem submeasurement_linear_bound {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized) (A : SubMeas Outcome ι) (ζ : Error)
    (hssc : BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A) ζ) :
    ∃ P : ProjSubMeas Outcome ι,
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.liftLeft)
        (constSubMeasFamily P.toSubMeas.liftLeft)
        (18 * ζ) := by
  classical
  let Ahat : Measurement (Option Outcome) ι := optionCompletion A
  have hAhatssc :
      BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily Ahat.toSubMeas) (2 * ζ) := by
    simpa [Ahat] using
      Orthonormalization.Completion.optionCompletion_bipartiteSSCRel
        (ψ := ψ) (hperm := hperm) (hψ := hψ) (A := A) (ζ := ζ) hssc
  have hLocalSSC :=
    MIPStarRE.LDT.Preliminaries.bipartiteSSC_implies_localSSC_liftLeft
      ψ hperm (uniformDistribution Unit)
      (constSubMeasFamily Ahat.toSubMeas) (2 * ζ) hAhatssc
  have hq : qSSCDefect ψ
      (leftLiftedMeasurement (ιB := ι) Ahat).toSubMeas ≤ 2 * ζ := by
    simpa [sscError, avgOver, uniformDistribution, constSubMeasFamily,
      IdxSubMeas.liftLeft, leftLiftedMeasurement, leftPlacedSubMeas,
      SubMeas.liftLeft] using hLocalSSC.diagonalOverlapBound
  have hsource :
      ∑ a, ev ψ
        ((leftLiftedMeasurement (ιB := ι) Ahat).outcome a -
          (leftLiftedMeasurement (ιB := ι) Ahat).outcome a *
            (leftLiftedMeasurement (ιB := ι) Ahat).outcome a) ≤ 2 * ζ :=
    sourceAlmostProjective_of_ssc ψ (leftLiftedMeasurement (ιB := ι) Ahat)
      (2 * ζ) hq
  rcases QuantumState.IsNormalized.nonempty (ι := ι × ι) hψ with ⟨⟨i, j⟩⟩
  letI : Nonempty ι := ⟨i⟩
  let φ : QuantumState ι := leftMarginalState ψ
  have hφ : φ.IsNormalized := leftMarginalState_isNormalized hψ
  have hterm (a : Option Outcome) :
      ev ψ
        ((leftLiftedMeasurement (ιB := ι) Ahat).outcome a -
          (leftLiftedMeasurement (ιB := ι) Ahat).outcome a *
            (leftLiftedMeasurement (ιB := ι) Ahat).outcome a) =
      ev φ (Ahat.outcome a - Ahat.outcome a * Ahat.outcome a) := by
    simpa [φ, leftLiftedMeasurement, leftPlacedSubMeas, leftTensor_sub,
      leftTensor_mul_leftTensor] using
      (leftMarginal_ev_eq (ψ := ψ)
        (X := Ahat.outcome a - Ahat.outcome a * Ahat.outcome a))
  have hdefect : idempotenceDefect φ Ahat ≤ 2 * ζ := by
    simpa [idempotenceDefect, hterm] using hsource
  obtain ⟨Phat, hPhat⟩ := exists_projective_measurement_linear_bound φ hφ Ahat
  have hdist :
      (∑ a : Option Outcome,
        ev φ (((Ahat.outcome a - Phat.outcome a)ᴴ) *
          (Ahat.outcome a - Phat.outcome a))) ≤ 18 * ζ := by
    calc
      (∑ a : Option Outcome,
        ev φ (((Ahat.outcome a - Phat.outcome a)ᴴ) *
          (Ahat.outcome a - Phat.outcome a))) ≤
          9 * idempotenceDefect φ Ahat := hPhat
      _ ≤ 9 * (2 * ζ) := by gcongr
      _ = 18 * ζ := by ring
  let Psub : ProjSubMeas (Option Outcome) ι :=
    { toSubMeas := Phat.toSubMeas
      proj := Phat.proj }
  have hlift (a : Option Outcome) :
      ev ψ (((leftTensor (ι₂ := ι) (Ahat.outcome a) -
        leftTensor (ι₂ := ι) (Psub.outcome a))ᴴ) *
        (leftTensor (ι₂ := ι) (Ahat.outcome a) -
          leftTensor (ι₂ := ι) (Psub.outcome a))) =
      ev φ (((Ahat.outcome a - Phat.outcome a)ᴴ) *
        (Ahat.outcome a - Phat.outcome a)) := by
    simpa [φ, Psub, leftTensor_sub, leftTensor_conjTranspose,
      leftTensor_mul_leftTensor] using
      (leftMarginal_ev_eq (ψ := ψ)
        (X := (Ahat.outcome a - Phat.outcome a)ᴴ *
          (Ahat.outcome a - Phat.outcome a)))
  have hcompleted : qSDD ψ Ahat.toSubMeas.liftLeft Psub.toSubMeas.liftLeft ≤
      18 * ζ := by
    unfold qSDD qSDDCore
    simpa only [SubMeas.liftLeft, mkLeftPlacedSubMeas_outcome] using
      (show (∑ a : Option Outcome,
        ev ψ (((leftTensor (ι₂ := ι) (Ahat.outcome a) -
          leftTensor (ι₂ := ι) (Psub.outcome a))ᴴ) *
          (leftTensor (ι₂ := ι) (Ahat.outcome a) -
            leftTensor (ι₂ := ι) (Psub.outcome a)))) ≤ 18 * ζ from by
        simpa only [hlift] using hdist)
  let P : ProjSubMeas Outcome ι := restrictSomeProjSubMeas Psub
  have hrestricted : qSDD ψ A.liftLeft P.toSubMeas.liftLeft ≤ 18 * ζ :=
    (Orthonormalization.Completion.qSDD_liftLeft_restrictSomeProjSubMeas_le
      (ψ := ψ) (A := A) (P := Psub)).trans hcompleted
  refine ⟨P, ?_⟩
  constructor
  simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily]
    using hrestricted

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
