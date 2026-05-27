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

namespace Orthonormalization
namespace ErrorBounds

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
    have hquarter : Real.rpow (2 : Error) (1 / (4 : Error)) ≤ 25 / 21 := by
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
    calc
      84 * Real.rpow (2 : Error) (1 / (4 : Error))
        ≤ 84 * (25 / 21 : Error) := by
            refine mul_le_mul_of_nonneg_left hquarter ?_
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

/-- Error bound for the completion-route proof of the orthonormalization theorem.
The completion step gives a `2ζ` self-consistency estimate; converting this to
a source-almost-projective estimate doubles the scalar to `4ζ`, and applying
the local `84·ζ^{1/4}` repair bound then gives the named envelope
`orthonormalizationCompletionRouteError ζ`. -/
lemma completionRouteError_bound
    (ζ : Error) (hζ : 0 ≤ ζ) :
    orthonormalizationMainLemmaError (consistencyToAlmostProjectiveError (2 * ζ)) ≤
      orthonormalizationCompletionRouteError ζ := by
  dsimp [orthonormalizationMainLemmaError, consistencyToAlmostProjectiveError,
    orthonormalizationCompletionRouteError]
  rw [show 2 * (2 * ζ) = 4 * ζ by ring]
  rw [Real.mul_rpow (by positivity : 0 ≤ (4 : Error)) hζ]
  have hcoeff_num : 84 * Real.rpow (4 : Error) (1 / (4 : Error)) ≤ 120 := by
    have hs_sq : (Real.rpow (4 : Error) (1 / (4 : Error))) ^ (2 : Nat) = 2 := by
      calc
        (Real.rpow (4 : Error) (1 / (4 : Error))) ^ (2 : Nat)
            = Real.rpow (4 : Error) ((1 / (4 : Error)) * 2) := by
                rw [← Real.rpow_natCast]
                simpa using (Real.rpow_mul (x := (4 : Error)) (by positivity)
                  (1 / (4 : Error)) 2).symm
        _ = 2 := by norm_num [Real.sqrt_eq_rpow]
    have hs_le : Real.rpow (4 : Error) (1 / (4 : Error)) ≤ 10 / 7 := by
      have hs_sq_le : (Real.rpow (4 : Error) (1 / (4 : Error))) ^ (2 : Nat) ≤
          (10 / 7 : Error) ^ (2 : Nat) := by
        nlinarith [hs_sq]
      nlinarith
    nlinarith
  have hzqr_nonneg : 0 ≤ Real.rpow ζ (1 / (4 : Error)) := Real.rpow_nonneg hζ _
  calc
    84 * (Real.rpow (4 : Error) (1 / (4 : Error)) *
        Real.rpow ζ (1 / (4 : Error)))
        = (84 * Real.rpow (4 : Error) (1 / (4 : Error))) *
            Real.rpow ζ (1 / (4 : Error)) := by ring
    _ ≤ 120 * Real.rpow ζ (1 / (4 : Error)) := by
          exact mul_le_mul_of_nonneg_right hcoeff_num hzqr_nonneg

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

end ErrorBounds
end Orthonormalization

end MIPStarRE.LDT.MakingMeasurementsProjective
