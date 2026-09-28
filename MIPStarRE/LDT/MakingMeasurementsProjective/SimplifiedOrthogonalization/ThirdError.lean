import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
import MIPStarRE.LDT.Basic.OperatorExpectations
import MIPStarRE.Quantum.FiniteMatrix.Order
import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.SelectedProjectors

/-!
# The third error family in linear orthogonalization

For any projective measurement `P` and positive contraction `T`, the family
`Pₐ(T - 1)` has squared state-dependent norm at most `φ(1 - T²)`.  This is the
last of the three estimates in the simplified proof.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`, last estimate after
  `eq:orthogonalization-decomposition`.
- `references/ldt-paper/orthonormalization.tex`, Section 5.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- The third error family is controlled by the defect of the polar positive
part `T`. -/
theorem third_error_le_one_sub_square {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (P : ProjMeas Outcome ι) (T : MIPStarRE.Quantum.Op ι)
    (hT_nonneg : 0 ≤ T) (hT_le_one : T ≤ 1) :
    (∑ a : Outcome,
      ev ψ (((P.outcome a * (T - 1))ᴴ) * (P.outcome a * (T - 1)))) ≤
      1 - ev ψ (T * T) := by
  have hT_self : Tᴴ = T :=
    (Matrix.nonneg_iff_posSemidef.mp hT_nonneg).isHermitian.eq
  have hpoint (a : Outcome) :
      ((P.outcome a * (T - 1))ᴴ) * (P.outcome a * (T - 1)) =
        (T - 1) * P.outcome a * (T - 1) := by
    have hP_self : (P.outcome a)ᴴ = P.outcome a := P.outcome_hermitian a
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hT_self,
      Matrix.conjTranspose_one, hP_self]
    simp only [mul_assoc]
    rw [← mul_assoc (P.outcome a) (P.outcome a) (T - 1), P.proj a]
  have hop :
      (∑ a : Outcome, (T - 1) * P.outcome a * (T - 1)) =
        (T - 1) * (T - 1) := by
    calc
      (∑ a : Outcome, (T - 1) * P.outcome a * (T - 1)) =
          (∑ a : Outcome, (T - 1) * P.outcome a) * (T - 1) := by
            rw [Finset.sum_mul]
      _ = ((T - 1) * (∑ a : Outcome, P.outcome a)) * (T - 1) := by
            rw [Matrix.mul_sum]
      _ = (T - 1) * (T - 1) := by rw [P.sum_eq, mul_one]
  have hsq : T * T ≤ T := MIPStarRE.Quantum.sq_le_self hT_nonneg hT_le_one
  have hsq_bound : (T - 1) * (T - 1) ≤ 1 - T * T := by
    have hnonneg : 0 ≤ (T - T * T) + (T - T * T) :=
      add_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr hsq)
    apply sub_nonneg.mp
    convert hnonneg using 1; noncomm_ring
  calc
    (∑ a : Outcome,
      ev ψ (((P.outcome a * (T - 1))ᴴ) * (P.outcome a * (T - 1)))) =
        ev ψ ((T - 1) * (T - 1)) := by
          simp_rw [hpoint]
          rw [← ev_sum, hop]
    _ ≤ ev ψ (1 - T * T) := ev_mono ψ _ _ hsq_bound
    _ = 1 - ev ψ (T * T) := by rw [ev_sub, ev_one_of_isNormalized ψ hψ]

/-- When `T²` is the sum of selected effects, their overlap bound controls the
third error family by the original defect. -/
theorem third_error_le_defect {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι))
    (P : ProjMeas Outcome ι) (T : MIPStarRE.Quantum.Op ι)
    (hT_nonneg : 0 ≤ T) (hT_le_one : T ≤ 1)
    (hT_square : T * T = ∑ a, selectedProjector M L a * M.outcome a)
    (hoverlap : 1 - idempotenceDefect ψ M ≤
      ∑ a, ev ψ (selectedProjector M L a * M.outcome a)) :
    (∑ a : Outcome,
      ev ψ (((P.outcome a * (T - 1))ᴴ) * (P.outcome a * (T - 1)))) ≤
      idempotenceDefect ψ M := by
  have hthird := third_error_le_one_sub_square ψ hψ P T hT_nonneg hT_le_one
  rw [hT_square, ev_sum] at hthird
  linarith

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
