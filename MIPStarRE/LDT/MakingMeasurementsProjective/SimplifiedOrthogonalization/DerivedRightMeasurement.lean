import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.RightConsistentMeasurements
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.ErrorBounds

/-!
# Original right-register interface from the linear bound

The `18 ζ` right-register result supplies the earlier fourth-root envelope
for `ζ ≤ 1`. For larger `ζ`, the zero projective submeasurement has distance
at most one, below the earlier envelope.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `lem:orthonormalization-main-lemma`.
- `references/ldt-paper/projectivization.tex`, for the right-register
  counterpart used by `thm:main-formal`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective

/-- Derive the earlier right-register projectivization envelope from the
linear bound and a unit-error fallback. -/
theorem right_measurement_from_linear {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB)
    (ζ : Error) (hζ : 0 ≤ ζ)
    (hCons : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ) :
    ∃ P : ProjSubMeas Outcome ιB,
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P.toSubMeas))
        (orthonormalizationError ζ) := by
  classical
  by_cases hsmall : ζ ≤ 1
  · obtain ⟨P, hP⟩ := right_consistent_measurement_linear_bound ψ hψ A B ζ hCons
    let Q : ProjSubMeas Outcome ιB :=
      { toSubMeas := P.toSubMeas
        proj := P.proj }
    refine ⟨Q, ?_⟩
    have hlinear : SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q.toSubMeas))
        (18 * ζ) := by simpa [Q] using hP
    rcases hlinear with ⟨hlinear⟩
    exact ⟨hlinear.trans (linear_le_orthonormalizationError ζ hζ hsmall)⟩
  · let Q : ProjSubMeas Outcome ιB := zeroProjSubMeas
    have hq : qSDD ψ
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas)
        (rightPlacedSubMeas (ιA := ιA) Q.toSubMeas) ≤ 1 := by
      simpa [Q] using qSDD_rightPlaced_zeroProjSubMeas_le_one ψ hψ B.toSubMeas
    refine ⟨Q, ?_⟩
    constructor
    have hq' : qSDD ψ
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas)
        (rightPlacedSubMeas (ιA := ιA) Q.toSubMeas) ≤
        orthonormalizationError ζ :=
      hq.trans (one_le_orthonormalizationError_of_one_le ζ (le_of_not_ge hsmall))
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using hq'

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
