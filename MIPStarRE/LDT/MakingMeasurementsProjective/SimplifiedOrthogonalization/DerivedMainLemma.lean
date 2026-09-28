import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.ConsistentMeasurements
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.ErrorBounds

/-!
# Original complete-measurement interface from the linear bound

The new `18 ζ` result supplies the original complete-measurement
orthonormalization interface when `ζ ≤ 1`.  For larger `ζ`, the zero
projective submeasurement has distance at most one, which is below the
original fourth-root envelope.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `lem:orthonormalization-main-lemma`.
- `references/ldt-paper/orthonormalization.tex`,
  `lem:orthonormalization-main-lemma`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective

/-- Derive the original complete-measurement paper bound from the linear
orthogonalization lemma and a unit-error fallback. -/
theorem mainLemma_from_linear {Outcome ιA ιB : Type*}
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB)
    (ζ : Error) (hζ : 0 ≤ ζ)
    (hCons : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ) :
    ∃ P : ProjSubMeas Outcome ιA,
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P.toSubMeas))
        (orthonormalizationMainLemmaError ζ) := by
  classical
  by_cases hsmall : ζ ≤ 1
  · obtain ⟨P, hP⟩ := consistent_measurement_linear_bound ψ hψ A B ζ hCons
    let Q : ProjSubMeas Outcome ιA :=
      { toSubMeas := P.toSubMeas
        proj := P.proj }
    refine ⟨Q, ?_⟩
    have hlinear : SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q.toSubMeas))
        (18 * ζ) := by simpa [Q] using hP
    rcases hlinear with ⟨hlinear⟩
    exact ⟨hlinear.trans (linear_le_mainLemmaError ζ hζ hsmall)⟩
  · let Q : ProjSubMeas Outcome ιA := zeroProjSubMeas
    have hq : qSDD ψ
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (leftPlacedSubMeas (ιB := ιB) Q.toSubMeas) ≤ 1 := by
      simpa [Q] using qSDD_leftPlaced_zeroProjSubMeas_le_one ψ hψ A.toSubMeas
    refine ⟨Q, ?_⟩
    constructor
    have hq' : qSDD ψ
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (leftPlacedSubMeas (ιB := ιB) Q.toSubMeas) ≤
        orthonormalizationMainLemmaError ζ :=
      hq.trans (one_le_mainLemmaError_of_one_le ζ (le_of_not_ge hsmall))
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using hq'

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
