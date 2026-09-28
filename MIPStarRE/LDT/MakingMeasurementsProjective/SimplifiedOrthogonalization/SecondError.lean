import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.PolarAlgebra
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.SelectedProjectors
import MIPStarRE.LDT.Basic.OperatorExpectations
import MIPStarRE.Quantum.FiniteMatrix.Order

/-!
# The middle error in linear orthogonalization

The middle error family is controlled by the square defect of the compressed
effect `T Pₐ T`.  This file records the pointwise operator inequality, which
can be summed once the coordinate compression `T Pₐ T = Qₐ Mₐ` is constructed.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`, second estimate after
  `eq:orthogonalization-decomposition`.
- `references/ldt-paper/orthonormalization.tex`, Section 5.
-/

open scoped MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- For a projection `P` and positive contraction `T`, the middle error is
bounded by the square defect of `T P T`. -/
theorem second_error_le_compressed_defect {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (P T : MIPStarRE.Quantum.Op ι)
    (hP : MIPStarRE.Quantum.IsProj P)
    (hT_nonneg : 0 ≤ T) (hT_le_one : T ≤ 1) :
    ev ψ ((((T - 1) * P * T)ᴴ) * ((T - 1) * P * T)) ≤
      ev ψ (T * P * T - (T * P * T) * (T * P * T)) := by
  have hT_self : Tᴴ = T :=
    (Matrix.nonneg_iff_posSemidef.mp hT_nonneg).isHermitian.eq
  have hP_self : Pᴴ = P := by
    exact hP.isSelfAdjoint.isHermitian.eq
  have hsq : T * T ≤ T := MIPStarRE.Quantum.sq_le_self hT_nonneg hT_le_one
  have hsq_bound : (T - 1) * (T - 1) ≤ 1 - T * T := by
    have hnonneg : 0 ≤ (T - T * T) + (T - T * T) :=
      add_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr hsq)
    apply sub_nonneg.mp
    convert hnonneg using 1; noncomm_ring
  have hconj :
      (P * T)ᴴ * ((T - 1) * (T - 1)) * (P * T) ≤
        (P * T)ᴴ * (1 - T * T) * (P * T) := by
    simpa [Matrix.star_eq_conjTranspose] using
      (star_left_conjugate_le_conjugate hsq_bound (P * T))
  have hleft :
      (((T - 1) * P * T)ᴴ) * ((T - 1) * P * T) =
        (P * T)ᴴ * ((T - 1) * (T - 1)) * (P * T) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hT_self, hP_self]
    noncomm_ring
  have hright :
      (P * T)ᴴ * (1 - T * T) * (P * T) =
        T * P * (1 - T * T) * P * T := by
    rw [Matrix.conjTranspose_mul, hT_self, hP_self]
    noncomm_ring
  calc
    ev ψ ((((T - 1) * P * T)ᴴ) * ((T - 1) * P * T)) =
        ev ψ ((P * T)ᴴ * ((T - 1) * (T - 1)) * (P * T)) := by rw [hleft]
    _ ≤ ev ψ ((P * T)ᴴ * (1 - T * T) * (P * T)) := ev_mono ψ _ _ hconj
    _ = ev ψ (T * P * T - (T * P * T) * (T * P * T)) := by
          rw [hright, compressed_square_defect T P hP.isIdempotentElem.eq]

/-- The total square defect of the selected effects is bounded by the
idempotence defect of the original measurement. -/
theorem selected_effect_square_defect_le_defect {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (M : Measurement Outcome ι)
    (L : Finset (Outcome × ι)) :
    (∑ a : Outcome,
      ev ψ (selectedProjector M L a * M.outcome a -
        (selectedProjector M L a * M.outcome a) *
          (selectedProjector M L a * M.outcome a))) ≤
      idempotenceDefect ψ M := by
  have hpoint (a : Outcome) :
      ev ψ (selectedProjector M L a * M.outcome a -
        (selectedProjector M L a * M.outcome a) *
          (selectedProjector M L a * M.outcome a)) ≤
      ev ψ (M.outcome a - M.outcome a * M.outcome a) := by
    let Q := selectedProjector M L a
    let A := M.outcome a
    let D := A - A * A
    have hQ : MIPStarRE.Quantum.IsProj Q := selectedProjector_isProj M L a
    have hA_nonneg : 0 ≤ A := M.outcome_pos a
    have hA_le_one : A ≤ 1 := M.outcome_le_one a
    have hD_nonneg : 0 ≤ D :=
      sub_nonneg.mpr (MIPStarRE.Quantum.sq_le_self hA_nonneg hA_le_one)
    have hcomm : Commute Q A := selectedProjector_commutes M L a
    have hcommD : Commute Q D := by
      dsimp [D]
      simpa [pow_two] using hcomm.sub_right (hcomm.pow_right 2)
    have hcomm' : Commute (1 - Q) D :=
      (Commute.one_left D).sub_left hcommD
    have hQD_le : Q * D ≤ D := by
      have hpos : 0 ≤ (1 - Q) * D :=
        Commute.mul_nonneg hQ.one_sub_nonneg hD_nonneg hcomm'
      exact sub_nonneg.mp (by simpa [sub_mul] using hpos)
    have hC_square : (Q * A) * (Q * A) = Q * (A * A) := by
      calc
        (Q * A) * (Q * A) = Q * (A * Q) * A := by noncomm_ring
        _ = Q * (Q * A) * A := by rw [hcomm.eq]
        _ = (Q * Q) * (A * A) := by noncomm_ring
        _ = Q * (A * A) := by rw [hQ.isIdempotentElem.eq]
    have hdefect : Q * A - (Q * A) * (Q * A) = Q * D := by
      rw [hC_square]
      simp [D, mul_sub]
    rw [hdefect]
    exact ev_mono ψ _ _ hQD_le
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  exact hsum

/-- Once the polar-coordinate identity identifies `T Pₐ T` with `QₐMₐ`,
the middle error family is bounded by the original defect. -/
theorem second_error_le_defect {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (M : Measurement Outcome ι)
    (L : Finset (Outcome × ι)) (P : ProjMeas Outcome ι)
    (T : MIPStarRE.Quantum.Op ι) (hT_nonneg : 0 ≤ T) (hT_le_one : T ≤ 1)
    (hcompression : ∀ a, T * P.outcome a * T =
      selectedProjector M L a * M.outcome a) :
    (∑ a : Outcome,
      ev ψ (((T - 1) * P.outcome a * T)ᴴ *
        ((T - 1) * P.outcome a * T))) ≤ idempotenceDefect ψ M := by
  calc
    (∑ a : Outcome,
      ev ψ (((T - 1) * P.outcome a * T)ᴴ *
        ((T - 1) * P.outcome a * T))) ≤
        ∑ a : Outcome,
          ev ψ (T * P.outcome a * T -
            (T * P.outcome a * T) * (T * P.outcome a * T)) := by
          apply Finset.sum_le_sum
          intro a _
          have hPa : MIPStarRE.Quantum.IsProj (P.outcome a) :=
            { isIdempotentElem := P.proj a
              isSelfAdjoint :=
                (show (P.outcome a).IsHermitian from P.outcome_hermitian a).isSelfAdjoint }
          exact second_error_le_compressed_defect ψ (P.outcome a) T hPa
            hT_nonneg hT_le_one
    _ = ∑ a : Outcome,
          ev ψ (selectedProjector M L a * M.outcome a -
            (selectedProjector M L a * M.outcome a) *
              (selectedProjector M L a * M.outcome a)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hcompression a]
    _ ≤ idempotenceDefect ψ M := selected_effect_square_defect_le_defect ψ M L

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
