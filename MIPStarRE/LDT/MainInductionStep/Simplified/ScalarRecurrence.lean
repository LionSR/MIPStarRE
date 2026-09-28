import MIPStarRE.LDT.MainInductionStep.Simplified.ScalarPowers

/-!
# Coefficient absorption in the simplified successor step

The inherited error, the new dilation error, and the quadratic pasting
cost fit below the next-dimension coefficient `1000 d² (m+1)⁴`.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT

/-- The product of the square-root dimension factor and its
one-eighth-power successor factor is at most the successor dimension. -/
theorem sqrt_mul_eighth_successor_le_successor
    (M : Error) (hM : 1 ≤ M) :
    Real.sqrt M * Real.rpow (M + 1) (1 / (8 : Error)) ≤ M + 1 := by
  have hN : 0 ≤ M + 1 := by linarith
  have hN1 : 1 ≤ M + 1 := by linarith
  have hroot : Real.sqrt M ≤ Real.sqrt (M + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hpow :
      Real.rpow (M + 1) (1 / (8 : Error)) ≤ Real.sqrt (M + 1) := by
    calc
      Real.rpow (M + 1) (1 / (8 : Error)) ≤
          Real.rpow (M + 1) (1 / (2 : Error)) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = Real.sqrt (M + 1) := by
        simpa using (Real.sqrt_eq_rpow (M + 1)).symm
  calc
    Real.sqrt M * Real.rpow (M + 1) (1 / (8 : Error)) ≤
        Real.sqrt (M + 1) * Real.sqrt (M + 1) := by
      exact mul_le_mul hroot hpow
        (Real.rpow_nonneg hN _) (Real.sqrt_nonneg _)
    _ = M + 1 := Real.mul_self_sqrt hN

/-- The numerical recurrence underlying the positive-degree successor
bound. Here `σ` and `ζ` are the mean recursive and dilation errors, and
`s` is the five-term eighth-power pasting sum. -/
theorem simplified_successor_coefficient_absorption
    (M D S σ ζ s : Error)
    (hM : 1 ≤ M) (hD : 1 ≤ D) (hS : 0 ≤ S)
    (hσ : σ ≤ 1000 * D ^ (2 : ℕ) * M ^ (4 : ℕ) *
      ((M + 1) / M) * S)
    (hζ : ζ ≤ 200 * (M + 1) * S)
    (hs : s ≤ 4 * Real.rpow (M + 1) (1 / (8 : Error)) * S) :
    ((M + 1) / M) * (σ + ζ) +
      21 * (M + 1) ^ (2 : ℕ) * D ^ (2 : ℕ) *
        Real.sqrt M * s ≤
      1000 * D ^ (2 : ℕ) * (M + 1) ^ (4 : ℕ) * S := by
  let N : Error := M + 1
  let c : Error := N / M
  have hM0 : 0 < M := by linarith
  have hN0 : 0 ≤ N := by dsimp [N]; linarith
  have hc0 : 0 ≤ c := div_nonneg hN0 (le_of_lt hM0)
  have hc_le_N : c ≤ N := by
    dsimp [c]
    exact div_le_self hN0 hM
  have hD2 : 1 ≤ D ^ (2 : ℕ) := by nlinarith
  have hfactor : 0 ≤ D ^ (2 : ℕ) * N ^ (2 : ℕ) * S := by positivity
  have hroot := sqrt_mul_eighth_successor_le_successor M hM
  have hσscale :
      c * σ ≤ 1000 * D ^ (2 : ℕ) * M ^ (2 : ℕ) *
        N ^ (2 : ℕ) * S := by
    calc
      c * σ ≤ c * (1000 * D ^ (2 : ℕ) * M ^ (4 : ℕ) * c * S) :=
        mul_le_mul_of_nonneg_left hσ hc0
      _ = _ := by
        dsimp [c, N]
        field_simp
  have hζscale :
      c * ζ ≤ 200 * N ^ (2 : ℕ) * S := by
    calc
      c * ζ ≤ c * (200 * N * S) := mul_le_mul_of_nonneg_left hζ hc0
      _ ≤ N * (200 * N * S) := by
        exact mul_le_mul_of_nonneg_right hc_le_N (by positivity)
      _ = _ := by ring
  have hpaste :
      21 * N ^ (2 : ℕ) * D ^ (2 : ℕ) * Real.sqrt M * s ≤
        84 * D ^ (2 : ℕ) * N ^ (3 : ℕ) * S := by
    have hcoef : 0 ≤ 21 * N ^ (2 : ℕ) * D ^ (2 : ℕ) *
        Real.sqrt M := by positivity
    calc
      21 * N ^ (2 : ℕ) * D ^ (2 : ℕ) * Real.sqrt M * s ≤
          (21 * N ^ (2 : ℕ) * D ^ (2 : ℕ) * Real.sqrt M) *
            (4 * Real.rpow N (1 / (8 : Error)) * S) :=
        mul_le_mul_of_nonneg_left (by simpa [N] using hs) hcoef
      _ = (84 * D ^ (2 : ℕ) * N ^ (2 : ℕ) * S) *
            (Real.sqrt M * Real.rpow N (1 / (8 : Error))) := by ring
      _ ≤ (84 * D ^ (2 : ℕ) * N ^ (2 : ℕ) * S) * N := by
        exact mul_le_mul_of_nonneg_left (by simpa [N] using hroot) (by positivity)
      _ = _ := by ring
  have hcoef :
      1000 * M ^ (2 : ℕ) + 200 + 84 * N ≤
        1000 * N ^ (2 : ℕ) := by
    dsimp [N]
    nlinarith
  have htwohundred :
      200 * N ^ (2 : ℕ) * S ≤
        200 * D ^ (2 : ℕ) * N ^ (2 : ℕ) * S := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hD2)
      (mul_nonneg (sq_nonneg N) hS)]
  have hfinal :
      1000 * D ^ (2 : ℕ) * M ^ (2 : ℕ) * N ^ (2 : ℕ) * S +
        200 * N ^ (2 : ℕ) * S +
        84 * D ^ (2 : ℕ) * N ^ (3 : ℕ) * S ≤
      1000 * D ^ (2 : ℕ) * N ^ (4 : ℕ) * S := by
    have hmul := mul_le_mul_of_nonneg_right hcoef hfactor
    nlinarith [hmul, htwohundred]
  calc
    c * (σ + ζ) +
        21 * N ^ (2 : ℕ) * D ^ (2 : ℕ) * Real.sqrt M * s =
      c * σ + c * ζ +
        21 * N ^ (2 : ℕ) * D ^ (2 : ℕ) * Real.sqrt M * s := by ring
    _ ≤ 1000 * D ^ (2 : ℕ) * M ^ (2 : ℕ) * N ^ (2 : ℕ) * S +
        200 * N ^ (2 : ℕ) * S +
        84 * D ^ (2 : ℕ) * N ^ (3 : ℕ) * S := by
      linarith [hσscale, hζscale, hpaste]
    _ ≤ 1000 * D ^ (2 : ℕ) * N ^ (4 : ℕ) * S := hfinal
    _ = _ := rfl

end MIPStarRE.LDT.MainInductionStep
