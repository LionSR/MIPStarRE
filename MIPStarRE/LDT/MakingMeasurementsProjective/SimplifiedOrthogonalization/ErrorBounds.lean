import MIPStarRE.LDT.MakingMeasurementsProjective.Defs

/-!
# Error bounds for the linear orthogonalization route

The simplified blueprint proves a squared state-dependent distance bounded by
`18 * ζ` for both a consistent complete measurement and a strongly
self-consistent submeasurement.  These inequalities compare that bound with
the older fourth-root envelopes in the nontrivial regime `ζ ≤ 1`.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `lem:orthonormalization-main-lemma` and `thm:orthonormalization`.
- `references/ldt-paper/orthonormalization.tex`,
  `lem:orthonormalization-main-lemma` and `thm:orthonormalization`.
-/

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- In the nontrivial error regime, the new linear bound implies the original
paper's complete-measurement error envelope. -/
theorem linear_le_mainLemmaError (ζ : Error) (hζ : 0 ≤ ζ) (hζ_le : ζ ≤ 1) :
    18 * ζ ≤ orthonormalizationMainLemmaError ζ := by
  have hpower : ζ ≤ Real.rpow ζ (1 / (4 : Error)) :=
    Real.self_le_rpow_of_le_one hζ hζ_le (by norm_num)
  have hpower_nonneg : 0 ≤ Real.rpow ζ (1 / (4 : Error)) :=
    Real.rpow_nonneg hζ _
  dsimp [orthonormalizationMainLemmaError]
  calc
    18 * ζ ≤ 18 * Real.rpow ζ (1 / (4 : Error)) := by nlinarith only [hpower]
    _ ≤ 84 * Real.rpow ζ (1 / (4 : Error)) := by nlinarith only [hpower_nonneg]

/-- In the nontrivial error regime, the new linear bound implies the original
paper's submeasurement error envelope. -/
theorem linear_le_orthonormalizationError
    (ζ : Error) (hζ : 0 ≤ ζ) (hζ_le : ζ ≤ 1) :
    18 * ζ ≤ orthonormalizationError ζ := by
  have hpower : ζ ≤ Real.rpow ζ (1 / (4 : Error)) :=
    Real.self_le_rpow_of_le_one hζ hζ_le (by norm_num)
  have hpower_nonneg : 0 ≤ Real.rpow ζ (1 / (4 : Error)) :=
    Real.rpow_nonneg hζ _
  dsimp [orthonormalizationError]
  calc
    18 * ζ ≤ 18 * Real.rpow ζ (1 / (4 : Error)) := by nlinarith only [hpower]
    _ ≤ 100 * Real.rpow ζ (1 / (4 : Error)) := by nlinarith only [hpower_nonneg]

/-- The original complete-measurement envelope exceeds one when the error
parameter is at least one. -/
theorem one_le_mainLemmaError_of_one_le (ζ : Error) (hζ : 1 ≤ ζ) :
    1 ≤ orthonormalizationMainLemmaError ζ := by
  have hpower : 1 ≤ Real.rpow ζ (1 / (4 : Error)) :=
    Real.one_le_rpow hζ (by norm_num)
  dsimp [orthonormalizationMainLemmaError]
  calc
    (1 : Error) ≤ 84 * 1 := by norm_num
    _ ≤ 84 * Real.rpow ζ (1 / (4 : Error)) := by nlinarith only [hpower]

/-- The original submeasurement envelope exceeds one when the error parameter
is at least one. -/
theorem one_le_orthonormalizationError_of_one_le (ζ : Error) (hζ : 1 ≤ ζ) :
    1 ≤ orthonormalizationError ζ := by
  have hpower : 1 ≤ Real.rpow ζ (1 / (4 : Error)) :=
    Real.one_le_rpow hζ (by norm_num)
  dsimp [orthonormalizationError]
  calc
    (1 : Error) ≤ 100 * 1 := by norm_num
    _ ≤ 100 * Real.rpow ζ (1 / (4 : Error)) := by nlinarith only [hpower]

/-- The new linear error together with the unit-error fallback implies the
original complete-measurement envelope for every nonnegative `ζ`. -/
theorem min_one_linear_le_mainLemmaError (ζ : Error) (hζ : 0 ≤ ζ) :
    min 1 (18 * ζ) ≤ orthonormalizationMainLemmaError ζ := by
  by_cases hζ_le : ζ ≤ 1
  · exact (min_le_right _ _).trans (linear_le_mainLemmaError ζ hζ hζ_le)
  · exact (min_le_left _ _).trans
      (one_le_mainLemmaError_of_one_le ζ (le_of_not_ge hζ_le))

/-- The new linear error together with the unit-error fallback implies the
original submeasurement envelope for every nonnegative `ζ`. -/
theorem min_one_linear_le_orthonormalizationError (ζ : Error) (hζ : 0 ≤ ζ) :
    min 1 (18 * ζ) ≤ orthonormalizationError ζ := by
  by_cases hζ_le : ζ ≤ 1
  · exact (min_le_right _ _).trans (linear_le_orthonormalizationError ζ hζ hζ_le)
  · exact (min_le_left _ _).trans
      (one_le_orthonormalizationError_of_one_le ζ (le_of_not_ge hζ_le))

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
