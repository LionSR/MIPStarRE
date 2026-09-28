import MIPStarRE.LDT.MakingMeasurementsProjective.Defs

/-!
# Unitary conjugation of projective measurements

The polar extension transports the coordinate projectors back to the source
Hilbert space by conjugating with a unitary matrix.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`, the definition
  `Pₐ = U†EₐU` in the state-dependent orthogonalization proof.
- `references/ldt-paper/orthonormalization.tex`, Section 5.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- Conjugate a projective measurement by a unitary matrix. -/
noncomputable def unitaryConjugateProjMeas {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (E : ProjMeas Outcome ι) (U : MIPStarRE.Quantum.Op ι)
    (hUU : U * Uᴴ = 1) (hUstarU : Uᴴ * U = 1) :
    ProjMeas Outcome ι where
  outcome := fun a => Uᴴ * E.outcome a * U
  total := 1
  outcome_pos := by
    intro a
    simpa [Matrix.star_eq_conjTranspose] using
      (star_left_conjugate_nonneg (E.outcome_pos a) U)
  sum_eq_total := by
    calc
      (∑ a : Outcome, Uᴴ * E.outcome a * U) =
          Uᴴ * (∑ a : Outcome, E.outcome a) * U := by
            rw [Matrix.mul_sum, Finset.sum_mul]
      _ = Uᴴ * U := by rw [E.sum_eq, mul_one]
      _ = 1 := hUstarU
  total_le_one := le_rfl
  total_eq_one := rfl
  proj := by
    intro a
    calc
      (Uᴴ * E.outcome a * U) * (Uᴴ * E.outcome a * U) =
          Uᴴ * E.outcome a * (U * Uᴴ) * E.outcome a * U := by noncomm_ring
      _ = Uᴴ * E.outcome a * E.outcome a * U := by rw [hUU, mul_one]
      _ = Uᴴ * (E.outcome a * E.outcome a) * U := by noncomm_ring
      _ = Uᴴ * E.outcome a * U := by rw [E.proj a]

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
