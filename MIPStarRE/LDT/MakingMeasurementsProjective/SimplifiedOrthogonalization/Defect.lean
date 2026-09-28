import MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization

/-!
# The state-dependent idempotence defect

This file records the defect used by the linear orthogonalization lemma in
`blueprint/src/chapter/low_degree_simplified.tex`.  The two displayed forms of
the defect agree because a complete measurement sums to the identity.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `eq:orthogonalization-defect` and `lem:state-dependent-orthogonalization`.
- `references/ldt-paper/orthonormalization.tex`, Section 5.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- The state-dependent idempotence defect
`Σₐ φ(Mₐ − Mₐ²)` of a complete measurement. -/
noncomputable def idempotenceDefect {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (M : Measurement Outcome ι) : Error :=
  ∑ a, ev ψ (M.outcome a - M.outcome a * M.outcome a)

/-- The idempotence defect is nonnegative. -/
theorem idempotenceDefect_nonneg {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (M : Measurement Outcome ι) :
    0 ≤ idempotenceDefect ψ M := by
  exact sourceAlmostProjective_nonneg ψ M

/-- For a normalized state, the defect is
`1 − φ(Σₐ Mₐ²)`, as in the simplified proof. -/
theorem idempotenceDefect_eq_one_sub_sum_squares {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (M : Measurement Outcome ι) :
    idempotenceDefect ψ M =
      1 - ∑ a, ev ψ (M.outcome a * M.outcome a) := by
  have hmass : ∑ a, ev ψ (M.outcome a) = 1 := by
    rw [← ev_sum ψ M.outcome, M.sum_eq_total, M.total_eq_one]
    exact ev_one_of_isNormalized ψ hψ
  unfold idempotenceDefect
  simp_rw [ev_sub]
  rw [Finset.sum_sub_distrib, hmass]

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
