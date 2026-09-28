import MIPStarRE.LDT.MainInductionStep.Simplified.DegreeZeroConsistency

/-!
# Large-error branch of the simplified positive-degree induction

If an axis, self-consistency, or degree-to-field ratio parameter is at
least one, the displayed positive-degree error is at least one. The
normalized consistency defect is then covered by a complete
distinguished-outcome measurement.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

/-- In positive degree, any of the three large parameter branches makes
the simplified induction error at least one. -/
theorem one_le_simplifiedMainInductionError_of_large_parameter
    (params : Parameters)
    (eps delta gamma : Error)
    (hd : 0 < params.d)
    (heps0 : 0 ≤ eps) (hdelta0 : 0 ≤ delta) (hgamma0 : 0 ≤ gamma)
    (hlarge : 1 ≤ eps ∨ 1 ≤ delta ∨
      1 ≤ ((params.d : Error) / (params.q : Error))) :
    1 ≤ simplifiedMainInductionError params eps delta gamma := by
  have hm1 : (1 : Error) ≤ params.m := by exact_mod_cast params.hm
  have hd1 : (1 : Error) ≤ params.d := by exact_mod_cast hd
  have hcoef : (1 : Error) ≤
      1000 * (params.d : Error) ^ (2 : ℕ) * (params.m : Error) ^ (4 : ℕ) := by
    have hD : (1 : Error) ≤ (params.d : Error) ^ (2 : ℕ) := by
      exact one_le_pow₀ hd1
    have hM : (1 : Error) ≤ (params.m : Error) ^ (4 : ℕ) := by
      exact one_le_pow₀ hm1
    nlinarith [mul_nonneg (sub_nonneg.mpr hD) (sub_nonneg.mpr hM)]
  have hratio0 : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  have hsum : 1 ≤ simplifiedPositiveErrorSum params eps delta gamma := by
    dsimp [simplifiedPositiveErrorSum]
    have hepsPow := Real.rpow_nonneg heps0 (1 / (32 : Error))
    have hdeltaPow := Real.rpow_nonneg hdelta0 (1 / (32 : Error))
    have hratioPow := Real.rpow_nonneg hratio0 (1 / (32 : Error))
    have hgammaPow := Real.rpow_nonneg hgamma0 (1 / (8 : Error))
    change 0 ≤ eps ^ (1 / (32 : Error)) at hepsPow
    change 0 ≤ delta ^ (1 / (32 : Error)) at hdeltaPow
    change 0 ≤ ((params.d : Error) / (params.q : Error)) ^
      (1 / (32 : Error)) at hratioPow
    change 0 ≤ gamma ^ (1 / (8 : Error)) at hgammaPow
    rcases hlarge with h | h | h
    · have hp := Real.one_le_rpow h (by norm_num : (0 : Error) ≤ 1 / 32)
      change 1 ≤ eps ^ (1 / (32 : Error)) at hp
      linarith
    · have hp := Real.one_le_rpow h (by norm_num : (0 : Error) ≤ 1 / 32)
      change 1 ≤ delta ^ (1 / (32 : Error)) at hp
      linarith
    · have hp := Real.one_le_rpow h (by norm_num : (0 : Error) ≤ 1 / 32)
      change 1 ≤ ((params.d : Error) / (params.q : Error)) ^
        (1 / (32 : Error)) at hp
      linarith
  have hS0 : 0 ≤ simplifiedPositiveErrorSum params eps delta gamma := by
    exact le_trans zero_le_one hsum
  have hprod : 1 ≤
      (1000 * (params.d : Error) ^ (2 : ℕ) *
        (params.m : Error) ^ (4 : ℕ)) *
        simplifiedPositiveErrorSum params eps delta gamma := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) hS0]
  simpa [simplifiedMainInductionError, Nat.ne_of_gt hd,
    simplifiedPositiveDegreeError, simplifiedPositiveErrorSum] using hprod

end MIPStarRE.LDT.MainInductionStep
