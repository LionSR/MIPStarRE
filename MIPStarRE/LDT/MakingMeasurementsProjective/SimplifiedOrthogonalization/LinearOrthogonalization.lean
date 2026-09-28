import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.PolarConstruction
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.PolarPositivePart
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.UnitaryConjugation
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.FirstError
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.SecondError
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.ThirdError
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.ThreeErrors

/-!
# Linear state-dependent orthogonalization

This is the finite-dimensional state-dependent orthogonalization lemma in the
simplified blueprint.  It combines global spectral rank allocation, a square
polar extension, and the three family-distance estimates to obtain the linear
bound `9 Δ`.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `lem:state-dependent-orthogonalization` and `eq:linear-orthogonalization`.
- `references/ldt-paper/orthonormalization.tex`, Section 5, for the earlier
  orthonormalization theorem that this lemma strengthens.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- `lem:state-dependent-orthogonalization`: a complete measurement has a
projective rounding whose squared state-dependent distance is at most nine
times its idempotence defect. -/
theorem exists_projective_measurement_linear_bound {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (M : Measurement Outcome ι) :
    ∃ P : ProjMeas Outcome ι,
      (∑ a : Outcome,
        ev ψ (((M.outcome a - P.outcome a)ᴴ) *
          (M.outcome a - P.outcome a))) ≤ 9 * idempotenceDefect ψ M := by
  classical
  obtain ⟨L, hcard, hoverlap_spec⟩ := exists_selected_overlap_ge_one_sub_defect ψ hψ M
  have hoverlap : 1 - idempotenceDefect ψ M ≤
      ∑ a, ev ψ (selectedProjector M L a * M.outcome a) := by
    rw [sum_ev_selectedProjector_mul_effect]
    exact hoverlap_spec
  let e : ι ≃ SelectedCarrier L := selectedCarrierEquiv L hcard
  let X := selectedPolarMatrix M L e
  have hgram : Xᴴ * X = selectedEffectSum M L := by
    simpa [X, selectedEffectSum] using selectedPolarMatrix_gram M L e
  obtain ⟨U, hUU, hUstarU, hX⟩ := exists_unitary_polar_factor X
  let T := selectedPolarPositivePart M L
  have hT := selectedPolarPositivePart_properties M L
  have hT_self : Tᴴ = T :=
    (Matrix.nonneg_iff_posSemidef.mp hT.1).isHermitian.eq
  have hT_square : T * T =
      ∑ a, selectedProjector M L a * M.outcome a := hT.2.2
  have hXUT : X = U * T := by
    rw [hgram] at hX
    exact hX
  let E := selectedCoordinateMeasurement L e
  let P : ProjMeas Outcome ι := unitaryConjugateProjMeas E U hUU hUstarU
  have hcompression (a : Outcome) : T * P.outcome a * T =
      selectedProjector M L a * M.outcome a := by
    calc
      T * P.outcome a * T = Xᴴ * E.outcome a * X := by
        exact polar_coordinate_identity X U T (E.outcome a) hXUT hT_self
      _ = selectedProjector M L a * M.outcome a := by
        exact selectedPolarMatrix_coordinate_compression M L e a
  have hfirst := first_error_le_defect ψ hψ M L hoverlap
  have hsecond := second_error_le_defect ψ M L P T hT.1 hT.2.1 hcompression
  have hthird := third_error_le_defect ψ hψ M L P T hT.1 hT.2.1
    hT_square hoverlap
  have hthree := three_error_families_le_nine ψ
    (fun a => (1 - selectedProjector M L a) * M.outcome a)
    (fun a => (T - 1) * P.outcome a * T)
    (fun a => P.outcome a * (T - 1))
    (idempotenceDefect ψ M) hfirst hsecond hthird
  refine ⟨P, ?_⟩
  calc
    (∑ a : Outcome,
      ev ψ (((M.outcome a - P.outcome a)ᴴ) *
        (M.outcome a - P.outcome a))) =
        ∑ a : Outcome,
          ev ψ ((((1 - selectedProjector M L a) * M.outcome a +
            (T - 1) * P.outcome a * T + P.outcome a * (T - 1))ᴴ) *
            ((1 - selectedProjector M L a) * M.outcome a +
            (T - 1) * P.outcome a * T + P.outcome a * (T - 1))) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [orthogonalization_decomposition (M.outcome a)
            (selectedProjector M L a) (P.outcome a) T (hcompression a)]
    _ ≤ 9 * idempotenceDefect ψ M := hthree

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
