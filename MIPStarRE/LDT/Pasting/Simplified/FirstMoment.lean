import MIPStarRE.LDT.Basic.DistributionAvg

/-!
# First-moment bound for the number of successful slices

A bounded success count is at most `d` unless interpolation is possible,
and at most `k` otherwise. Averaging this pointwise inequality gives the
first-moment lower bound on interpolation probability.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:first-success-completeness`.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators

/-- A bounded count is controlled by the indicator that it reaches `d + 1`. -/
theorem success_count_le_threshold_indicator
    {Ω : Type*} (N : Ω → ℕ) (k d : ℕ)
    (hN : ∀ ω, N ω ≤ k) (ω : Ω) :
    (N ω : Error) ≤ (d : Error) +
      ((k - d : ℕ) : Error) * (if d + 1 ≤ N ω then 1 else 0) := by
  by_cases h : d + 1 ≤ N ω
  · have hdk : d ≤ k := (Nat.le_of_lt h).trans (hN ω)
    simp only [if_pos h, mul_one]
    have heq : (d : Error) + ((k - d : ℕ) : Error) = (k : Error) := by
      exact_mod_cast Nat.add_sub_of_le hdk
    rw [heq]
    exact_mod_cast hN ω
  · simp only [if_neg h, mul_zero, add_zero]
    have hle : N ω ≤ d := by omega
    exact_mod_cast hle

/-- The probability of at least `d + 1` successes is bounded below by
the normalized excess of the expected success count over `d`. -/
theorem threshold_probability_ge_first_moment
    {Ω : Type*} (D : Distribution Ω) (hD : D.IsProbability)
    (N : Ω → ℕ) (k d : ℕ) (hN : ∀ ω, N ω ≤ k)
    (hdk : d < k) :
    (avgOver D (fun ω => (N ω : Error)) - (d : Error)) /
        ((k - d : ℕ) : Error) ≤
      avgOver D (fun ω => if d + 1 ≤ N ω then 1 else 0) := by
  have hpoint (ω : Ω) := success_count_le_threshold_indicator N k d hN ω
  have havg := avgOver_mono D (fun ω => (N ω : Error))
    (fun ω => (d : Error) + ((k - d : ℕ) : Error) *
      (if d + 1 ≤ N ω then 1 else 0)) hpoint
  rw [avgOver_add, avgOver_const_of_isProbability D hD,
    avgOver_const_mul] at havg
  have hpos : (0 : Error) < ((k - d : ℕ) : Error) := by
    exact_mod_cast Nat.sub_pos_of_lt hdk
  apply (div_le_iff₀ hpos).2
  nlinarith

end MIPStarRE.LDT.Pasting
