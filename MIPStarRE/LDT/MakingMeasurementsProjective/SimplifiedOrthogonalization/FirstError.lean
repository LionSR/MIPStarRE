import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.SelectedProjectors
import MIPStarRE.Quantum.FiniteMatrix.Order

/-!
# The first error family in linear orthogonalization

The discarded part `(1 - Qₐ)Mₐ` of an effect is a positive contraction.  Its
square is bounded by itself, and the global selected-overlap estimate controls
the sum of these errors.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`, first estimate after
  `eq:orthogonalization-decomposition`.
- `references/ldt-paper/orthonormalization.tex`, Section 5.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- The state-dependent squared error from discarding the unselected part of
each effect is at most the idempotence defect. -/
theorem first_error_le_defect {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι))
    (hoverlap : 1 - idempotenceDefect ψ M ≤
      ∑ a, ev ψ (selectedProjector M L a * M.outcome a)) :
    (∑ a : Outcome,
      ev ψ ((((1 - selectedProjector M L a) * M.outcome a)ᴴ) *
        ((1 - selectedProjector M L a) * M.outcome a))) ≤
      idempotenceDefect ψ M := by
  have hpoint (a : Outcome) :
      ev ψ ((((1 - selectedProjector M L a) * M.outcome a)ᴴ) *
        ((1 - selectedProjector M L a) * M.outcome a)) ≤
      ev ψ (M.outcome a) -
        ev ψ (selectedProjector M L a * M.outcome a) := by
    let Q := selectedProjector M L a
    let B := (1 - Q) * M.outcome a
    have hB_eq : B = M.outcome a - Q * M.outcome a := by
      dsimp [B]
      noncomm_ring
    have hbound := selectedProjector_mul_effect_nonneg_le M L a
    have hB_nonneg : 0 ≤ B := by
      rw [hB_eq]
      exact sub_nonneg.mpr hbound.2
    have hB_le : B ≤ 1 := by
      calc
        B = M.outcome a - Q * M.outcome a := hB_eq
        _ ≤ M.outcome a := sub_le_self _ hbound.1
        _ ≤ 1 := M.outcome_le_one a
    have hB_self : Bᴴ = B :=
      (Matrix.nonneg_iff_posSemidef.mp hB_nonneg).isHermitian.eq
    calc
      ev ψ (Bᴴ * B) = ev ψ (B * B) := by rw [hB_self]
      _ ≤ ev ψ B := ev_mono ψ _ _ (MIPStarRE.Quantum.sq_le_self hB_nonneg hB_le)
      _ = ev ψ (M.outcome a) - ev ψ (Q * M.outcome a) := by
            rw [hB_eq, ev_sub]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  have hmass : (∑ a : Outcome, ev ψ (M.outcome a)) = 1 := by
    rw [← ev_sum, M.sum_eq_total, M.total_eq_one]
    exact ev_one_of_isNormalized ψ hψ
  rw [Finset.sum_sub_distrib, hmass] at hsum
  linarith

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
