import MIPStarRE.LDT.MakingMeasurementsProjective.Defs

/-!
# Error Bounds for Orthonormalization

This file records the scalar estimates which compare the intermediate error
terms in the proof of the orthonormalization theorem with the paper's final
`100 * ζ ^ (1/4)` envelope.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

/-! ### Scalar estimates -/

/-- The quarter-root factor `2^{1/4}` is below the paper-friendly rational bound
`25/21`, which is exactly the slack needed to turn `84·(2ζ)^{1/4}` into
`100·ζ^{1/4}`. -/
lemma quarterRootTwo_le_twentyFiveTwentyOne :
    Real.rpow (2 : Error) (1 / (4 : Error)) ≤ 25 / 21 := by
  let x : Error := Real.rpow (2 : Error) (1 / (4 : Error))
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg (by norm_num) _
  have hx4 : x ^ (4 : ℕ) = 2 := by
    change (Real.rpow (2 : Error) (1 / (4 : Error))) ^ (4 : ℕ) = 2
    calc
      (Real.rpow (2 : Error) (1 / (4 : Error))) ^ (4 : ℕ)
          = (Real.rpow (2 : Error) (1 / (4 : Error))) ^ (4 : Error) := by
              symm
              exact Real.rpow_natCast _ 4
      _ = Real.rpow (2 : Error) ((1 / (4 : Error)) * 4) := by
              simpa using
                (Real.rpow_mul (x := (2 : Error)) (by positivity)
                  (1 / (4 : Error)) 4).symm
      _ = Real.rpow (2 : Error) 1 := by norm_num
      _ = 2 := by norm_num [Real.rpow_natCast]
  by_contra hx_gt
  have hx_lt : (25 / 21 : Error) < x := lt_of_not_ge hx_gt
  have hpow_lt : (25 / 21 : Error) ^ (4 : ℕ) < x ^ (4 : ℕ) := by
    exact pow_lt_pow_left₀ hx_lt (by positivity) (by decide)
  have hq : (2 : Error) < (25 / 21 : Error) ^ (4 : ℕ) := by
    norm_num
  have : (25 / 21 : Error) ^ (4 : ℕ) < 2 := by
    simpa [hx4] using hpow_lt
  linarith

/-- Bookkeeping for the submeasurement version of the orthonormalization theorem:
after completing `A` by a fresh outcome, the local measurement lemma returns the
error `84·(2ζ)^{1/4}`, which is bounded by the paper's `100·ζ^{1/4}`. -/
lemma orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError
    (ζ : Error) (hζ : 0 ≤ ζ) :
    orthonormalizationMainLemmaError (2 * ζ) ≤ orthonormalizationError ζ := by
  dsimp [orthonormalizationMainLemmaError, orthonormalizationError]
  rw [Real.mul_rpow (by positivity) hζ]
  have hconst :
      84 * Real.rpow (2 : Error) (1 / (4 : Error)) ≤ 100 := by
    calc
      84 * Real.rpow (2 : Error) (1 / (4 : Error))
        ≤ 84 * (25 / 21 : Error) := by
            refine mul_le_mul_of_nonneg_left quarterRootTwo_le_twentyFiveTwentyOne ?_
            norm_num
      _ = 100 := by norm_num
  have hquart_nonneg : 0 ≤ Real.rpow ζ (1 / (4 : Error)) := Real.rpow_nonneg hζ _
  calc
    84 *
        (Real.rpow (2 : Error) (1 / (4 : Error)) *
          Real.rpow ζ (1 / (4 : Error))) =
      (84 * Real.rpow (2 : Error) (1 / (4 : Error))) *
        Real.rpow ζ (1 / (4 : Error)) := by ring
    _ ≤ 100 * Real.rpow ζ (1 / (4 : Error)) := by
          exact mul_le_mul_of_nonneg_right hconst hquart_nonneg

/-- In the large-`ζ` branch `ζ > 1/2`, the target bound `100·ζ^{1/4}` already
exceeds `1`, so the trivial zero projective submeasurement suffices. -/
lemma orthonormalizationError_ge_one_of_half_lt (ζ : Error)
    (hhalf_lt : (1 / 2 : Error) < ζ) :
    1 ≤ orthonormalizationError ζ := by
  dsimp [orthonormalizationError]
  have hhalf_rpow_le :
      Real.rpow (1 / 2 : Error) (1 / (4 : Error)) ≤
        Real.rpow ζ (1 / (4 : Error)) := by
    exact Real.rpow_le_rpow (by positivity) (le_of_lt hhalf_lt) (by positivity)
  have hhalf_le_root :
      (1 / 2 : Error) ≤ Real.rpow (1 / 2 : Error) (1 / (4 : Error)) := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge'
        (show 0 ≤ (1 / 2 : Error) by positivity)
        (show (1 / 2 : Error) ≤ 1 by norm_num)
        (show 0 ≤ (1 / (4 : Error)) by positivity)
        (by norm_num : (1 / (4 : Error)) ≤ 1))
  have hroot_lower : (1 / 2 : Error) ≤ Real.rpow ζ (1 / (4 : Error)) :=
    le_trans hhalf_le_root hhalf_rpow_le
  have h50_le : (50 : Error) ≤ 100 * Real.rpow ζ (1 / (4 : Error)) := by
    nlinarith
  exact (by norm_num : (1 : Error) ≤ 50).trans h50_le

/-- Error bookkeeping for the composition of `consistencyToAlmostProjective`
and `roundAlmostProjMeas`. -/
lemma orthonormalizationMainLemma_error_bound (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    roundingToProjectiveError (consistencyToAlmostProjectiveError ζ) ≤
      orthonormalizationMainLemmaError ζ := by
  /-
  The theorem below is structurally just the composition of
  `consistencyToAlmostProjective` and `roundAlmostProjMeas`.
  The remaining bookkeeping is the scalar inequality comparing the composed
  rounding bound with the named `orthonormalizationMainLemmaError`.
  -/
  dsimp [roundingToProjectiveError, consistencyToAlmostProjectiveError,
    orthonormalizationMainLemmaError]
  rw [Real.mul_rpow (by positivity) hζ]
  have hζrpow :
      Real.rpow ζ (1 / (2 : Error)) ≤ Real.rpow ζ (1 / (4 : Error)) := by
    refine Real.rpow_le_rpow_of_exponent_ge' hζ hζ1 ?_ ?_
    · positivity
    · norm_num
  have hsqrt_two_le_seven : Real.rpow (2 : Error) (1 / (2 : Error)) ≤ 7 := by
    have hsqrt_two_le_two : Real.rpow (2 : Error) (1 / (2 : Error)) ≤ 2 := by
      simpa using
        (Real.rpow_le_self_of_one_le
          (h₁ := (by norm_num : (1 : Error) ≤ 2))
          (h₂ := (by norm_num : (1 / (2 : Error)) ≤ 1)))
    exact hsqrt_two_le_two.trans (by norm_num)
  have hquarter_nonneg : 0 ≤ Real.rpow ζ (1 / (4 : Error)) := Real.rpow_nonneg hζ _
  calc
    12 * (Real.rpow (2 : Error) (1 / (2 : Error)) * Real.rpow ζ (1 / (2 : Error)))
      ≤ 12 * (Real.rpow (2 : Error) (1 / (2 : Error)) * Real.rpow ζ (1 / (4 : Error))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hζrpow (Real.rpow_nonneg (by norm_num) _)
    _ = (12 * Real.rpow (2 : Error) (1 / (2 : Error))) * Real.rpow ζ (1 / (4 : Error)) := by
      ring
    _ ≤ 84 * Real.rpow ζ (1 / (4 : Error)) := by
      refine mul_le_mul_of_nonneg_right ?_ hquarter_nonneg
      have hcoeff : 12 * Real.rpow (2 : Error) (1 / (2 : Error)) ≤ 12 * 7 := by
        exact mul_le_mul_of_nonneg_left hsqrt_two_le_seven (by norm_num)
      simpa using hcoeff.trans_eq (by norm_num : (12 : Error) * 7 = 84)

/-- The scalar weakening `84·ζ^{1/4} ≤ 100·ζ^{1/4}` from the local
orthonormalization bound to the paper's error term. Factored out as a named
lemma because the same bookkeeping reappears in any top-level theorem that
derives `orthonormalization` from `orthonormalizationMeasurement` via
submeasurement completion. -/
lemma orthonormalizationMainLemmaError_le_orthonormalizationError
    (ζ : Error) (hζ : 0 ≤ ζ) :
    orthonormalizationMainLemmaError ζ ≤ orthonormalizationError ζ := by
  dsimp [orthonormalizationMainLemmaError, orthonormalizationError]
  exact mul_le_mul_of_nonneg_right
    (by norm_num : (84 : Error) ≤ 100) (Real.rpow_nonneg hζ _)

end MIPStarRE.LDT.MakingMeasurementsProjective
