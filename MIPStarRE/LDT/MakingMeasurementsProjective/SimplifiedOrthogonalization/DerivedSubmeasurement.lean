import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.Submeasurement
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.ErrorBounds

/-!
# Original submeasurement interface from the linear bound

The new `18 ζ` result supplies the original orthonormalization theorem when
`ζ ≤ 1`.  For larger `ζ`, the zero projective submeasurement has distance at
most one, below the original fourth-root envelope.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `thm:orthonormalization`.
- `references/ldt-paper/orthonormalization.tex`,
  `thm:orthonormalization`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective

/-- Derive the original submeasurement paper bound from the linear
orthogonalization theorem and a unit-error fallback. -/
theorem orthonormalization_from_linear {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized) (A : SubMeas Outcome ι) (ζ : Error)
    (hssc : BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A) ζ) :
    ∃ P : ProjSubMeas Outcome ι,
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.liftLeft)
        (constSubMeasFamily P.toSubMeas.liftLeft)
        (orthonormalizationError ζ) := by
  have hζ : 0 ≤ ζ :=
    le_trans
      (bipartiteSSCError_nonneg ψ (uniformDistribution Unit)
        (constSubMeasFamily A))
      hssc.overlapBound
  by_cases hsmall : ζ ≤ 1
  · obtain ⟨P, hP⟩ := submeasurement_linear_bound ψ hperm hψ A ζ hssc
    refine ⟨P, ?_⟩
    rcases hP with ⟨hP⟩
    exact ⟨hP.trans (linear_le_orthonormalizationError ζ hζ hsmall)⟩
  · let P : ProjSubMeas Outcome ι := zeroProjSubMeas
    have hq : qSDD ψ A.liftLeft P.toSubMeas.liftLeft ≤ 1 := by
      simpa [P, SubMeas.liftLeft, leftPlacedSubMeas] using
        qSDD_leftPlaced_zeroProjSubMeas_le_one ψ hψ A
    refine ⟨P, ?_⟩
    constructor
    have hq' : qSDD ψ A.liftLeft P.toSubMeas.liftLeft ≤
        orthonormalizationError ζ :=
      hq.trans (one_le_orthonormalizationError_of_one_le ζ (le_of_not_ge hsmall))
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using hq'

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
