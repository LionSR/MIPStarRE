import MIPStarRE.LDT.MainInductionStep.Simplified.ScalarAverages
import MIPStarRE.LDT.Pasting.Simplified.PastingScalarBounds

/-!
# Fractional-power bounds for simplified induction

The mean dilation error is raised to the eighth power in pasting. The
quarter-power intermediate bound ensures that this term fits the
one-thirty-second-power induction scale.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-induction`.
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open MIPStarRE.LDT.Pasting
open scoped BigOperators

/-- On the unit interval, the square-root term is bounded by the
quarter-power term. -/
theorem half_power_le_quarter_power
    (x : Error) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.rpow x (1 / (2 : Error)) ≤
      Real.rpow x (1 / (4 : Error)) := by
  exact Real.rpow_le_rpow_of_exponent_ge' hx0 hx1
    (by norm_num) (by norm_num)

/-- On the unit interval, an eighth-power term is bounded by its
one-thirty-second-power counterpart. -/
theorem eighth_power_le_thirtysecond_power
    (x : Error) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.rpow x (1 / (8 : Error)) ≤
      Real.rpow x (1 / (32 : Error)) := by
  exact Real.rpow_le_rpow_of_exponent_ge' hx0 hx1
    (by norm_num) (by norm_num)

/-- The averaged dilation error is bounded by a quarter-power sum in
the small-error regime. -/
theorem simplifiedAverageDilationError_le_quarter
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hratio1 : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    simplifiedAverageDilationError params restrictionPkg ≤
      200 * ((params.m + 1 : ℕ) : Error) *
        (Real.rpow eps (1 / (4 : Error)) +
          Real.rpow delta (1 / (4 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error))
            (1 / (4 : Error))) := by
  have hratio0 : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  have hroot := simplifiedAverageDilationError_le params strategy eps delta gamma
    restrictionPkg heps0 hdelta0
  have heps := half_power_le_quarter_power eps heps0 heps1
  have hdelta := half_power_le_quarter_power delta hdelta0 hdelta1
  have hratio := half_power_le_quarter_power _ hratio0 hratio1
  have hcoef : 0 ≤ 200 * ((params.m + 1 : ℕ) : Error) := by positivity
  exact hroot.trans (mul_le_mul_of_nonneg_left (by linarith) hcoef)

/-- The averaged dilation error also fits directly below the positive-degree
induction sum. -/
theorem simplifiedAverageDilationError_le_positive_sum
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (restrictionPkg : AnswerSliceRestrictionData params strategy eps delta gamma)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hgamma0 : 0 ≤ gamma)
    (hratio1 : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    simplifiedAverageDilationError params restrictionPkg ≤
      200 * ((params.m + 1 : ℕ) : Error) *
        simplifiedPositiveErrorSum params eps delta gamma := by
  have hratio0 : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  have hroot := simplifiedAverageDilationError_le params strategy eps delta gamma
    restrictionPkg heps0 hdelta0
  have heps : Real.rpow eps (1 / (2 : Error)) ≤
      Real.rpow eps (1 / (32 : Error)) :=
    Real.rpow_le_rpow_of_exponent_ge' heps0 heps1
      (by norm_num) (by norm_num)
  have hdelta : Real.rpow delta (1 / (2 : Error)) ≤
      Real.rpow delta (1 / (32 : Error)) :=
    Real.rpow_le_rpow_of_exponent_ge' hdelta0 hdelta1
      (by norm_num) (by norm_num)
  have hratio : Real.rpow ((params.d : Error) / (params.q : Error))
      (1 / (2 : Error)) ≤
      Real.rpow ((params.d : Error) / (params.q : Error))
        (1 / (32 : Error)) :=
    Real.rpow_le_rpow_of_exponent_ge' hratio0 hratio1
      (by norm_num) (by norm_num)
  have hinner :
      Real.rpow eps (1 / (2 : Error)) +
        Real.rpow delta (1 / (2 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (2 : Error)) ≤
      simplifiedPositiveErrorSum params eps delta gamma := by
    change eps ^ (1 / (2 : Error)) ≤ eps ^ (1 / (32 : Error)) at heps
    change delta ^ (1 / (2 : Error)) ≤ delta ^ (1 / (32 : Error)) at hdelta
    change (((params.d : Error) / (params.q : Error)) ^ (1 / (2 : Error))) ≤
      ((params.d : Error) / (params.q : Error)) ^ (1 / (32 : Error)) at hratio
    dsimp [simplifiedPositiveErrorSum]
    have hgamma := Real.rpow_nonneg hgamma0 (1 / (8 : Error))
    linarith
  exact hroot.trans
    (mul_le_mul_of_nonneg_left hinner (by positivity))

/-- The numerical coefficient `200` contributes less than a factor of two
after taking an eighth power. -/
theorem two_hundred_eighth_le_two :
    Real.rpow (200 : Error) (1 / (8 : Error)) ≤ 2 := by
  have h := (Real.rpow_inv_le_iff_of_pos
    (by norm_num : (0 : Error) ≤ 200)
    (by norm_num : (0 : Error) ≤ 2)
    (by norm_num : (0 : Error) < 8)).2 (by norm_num : (200 : Error) ≤ 2 ^ (8 : Error))
  simpa [one_div] using h

/-- Taking an eighth power of a sum of three quarter-power terms
produces the one-thirty-second-power sum. -/
theorem eighth_quarter_sum_le_thirtysecond_sum
    (a b c : Error) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.rpow
        (Real.rpow a (1 / (4 : Error)) +
          Real.rpow b (1 / (4 : Error)) +
          Real.rpow c (1 / (4 : Error)))
        (1 / (8 : Error)) ≤
      Real.rpow a (1 / (32 : Error)) +
        Real.rpow b (1 / (32 : Error)) +
        Real.rpow c (1 / (32 : Error)) := by
  have ha4 : 0 ≤ Real.rpow a (1 / (4 : Error)) := Real.rpow_nonneg ha _
  have hb4 : 0 ≤ Real.rpow b (1 / (4 : Error)) := Real.rpow_nonneg hb _
  have hc4 : 0 ≤ Real.rpow c (1 / (4 : Error)) := Real.rpow_nonneg hc _
  have hfirst := Real.rpow_add_le_add_rpow (add_nonneg ha4 hb4) hc4
    (by norm_num : 0 ≤ (1 / (8 : Error)))
    (by norm_num : (1 / (8 : Error)) ≤ 1)
  have hsecond := Real.rpow_add_le_add_rpow ha4 hb4
    (by norm_num : 0 ≤ (1 / (8 : Error)))
    (by norm_num : (1 / (8 : Error)) ≤ 1)
  have ha32 : Real.rpow (Real.rpow a (1 / (4 : Error)))
      (1 / (8 : Error)) = Real.rpow a (1 / (32 : Error)) := by
    calc
      _ = Real.rpow a ((1 / (4 : Error)) * (1 / (8 : Error))) :=
        (Real.rpow_mul ha _ _).symm
      _ = _ := by norm_num
  have hb32 : Real.rpow (Real.rpow b (1 / (4 : Error)))
      (1 / (8 : Error)) = Real.rpow b (1 / (32 : Error)) := by
    calc
      _ = Real.rpow b ((1 / (4 : Error)) * (1 / (8 : Error))) :=
        (Real.rpow_mul hb _ _).symm
      _ = _ := by norm_num
  have hc32 : Real.rpow (Real.rpow c (1 / (4 : Error)))
      (1 / (8 : Error)) = Real.rpow c (1 / (32 : Error)) := by
    calc
      _ = Real.rpow c ((1 / (4 : Error)) * (1 / (8 : Error))) :=
        (Real.rpow_mul hc _ _).symm
      _ = _ := by norm_num
  have hsum := hfirst.trans
    (add_le_add hsecond
      (le_refl (Real.rpow (Real.rpow c (1 / (4 : Error))) (1 / (8 : Error)))))
  change Real.rpow
      (Real.rpow a (1 / (4 : Error)) + Real.rpow b (1 / (4 : Error)) +
        Real.rpow c (1 / (4 : Error))) (1 / (8 : Error)) ≤
      Real.rpow (Real.rpow a (1 / (4 : Error))) (1 / (8 : Error)) +
        Real.rpow (Real.rpow b (1 / (4 : Error))) (1 / (8 : Error)) +
        Real.rpow (Real.rpow c (1 / (4 : Error))) (1 / (8 : Error)) at hsum
  simpa only [ha32, hb32, hc32] using hsum

/-- The eighth power of the averaged dilation error fits the
one-thirty-second-power ambient scale. -/
theorem dilation_eighth_le_positive_sum
    (params : Parameters)
    (eps delta zeta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hzeta : 0 ≤ zeta)
    (hquarter : zeta ≤
      200 * ((params.m + 1 : ℕ) : Error) *
        (Real.rpow eps (1 / (4 : Error)) +
          Real.rpow delta (1 / (4 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error))
            (1 / (4 : Error)))) :
    Real.rpow zeta (1 / (8 : Error)) ≤
      2 * Real.rpow (((params.m + 1 : ℕ) : Error)) (1 / (8 : Error)) *
        (Real.rpow eps (1 / (32 : Error)) +
          Real.rpow delta (1 / (32 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error))
            (1 / (32 : Error))) := by
  let n : Error := ((params.m + 1 : ℕ) : Error)
  let s4 : Error :=
    Real.rpow eps (1 / (4 : Error)) +
      Real.rpow delta (1 / (4 : Error)) +
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (4 : Error))
  let s32 : Error :=
    Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error))
  have hratio : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hs4 : 0 ≤ s4 := by
    dsimp [s4]
    positivity
  have hs32 : Real.rpow s4 (1 / (8 : Error)) ≤ s32 := by
    exact eighth_quarter_sum_le_thirtysecond_sum eps delta _ heps hdelta hratio
  have hnum : Real.rpow (200 : Error) (1 / (8 : Error)) ≤ 2 :=
    two_hundred_eighth_le_two
  calc
    Real.rpow zeta (1 / (8 : Error)) ≤
        Real.rpow (200 * n * s4) (1 / (8 : Error)) := by
      exact Real.rpow_le_rpow hzeta (by simpa [n, s4] using hquarter)
        (by norm_num)
    _ = Real.rpow (200 : Error) (1 / (8 : Error)) *
          Real.rpow n (1 / (8 : Error)) *
          Real.rpow s4 (1 / (8 : Error)) := by
      calc
        _ = Real.rpow (200 * n) (1 / (8 : Error)) *
            Real.rpow s4 (1 / (8 : Error)) :=
          Real.mul_rpow (by positivity : (0 : Error) ≤ 200 * n) hs4
        _ = _ := by
          rw [show Real.rpow (200 * n) (1 / (8 : Error)) =
              Real.rpow (200 : Error) (1 / (8 : Error)) *
                Real.rpow n (1 / (8 : Error)) from
            Real.mul_rpow (by norm_num : (0 : Error) ≤ 200) hn]
    _ ≤ 2 * Real.rpow n (1 / (8 : Error)) * s32 := by
      have hNpow : 0 ≤ Real.rpow n (1 / (8 : Error)) :=
        Real.rpow_nonneg hn _
      have hS4pow : 0 ≤ Real.rpow s4 (1 / (8 : Error)) :=
        Real.rpow_nonneg hs4 _
      have hleft := mul_le_mul_of_nonneg_right hnum
        (mul_nonneg hNpow hS4pow)
      have hright := mul_le_mul_of_nonneg_left hs32
        (mul_nonneg (by norm_num : (0 : Error) ≤ 2) hNpow)
      nlinarith [hleft, hright]
    _ = _ := rfl

/-- The entire five-term pasting sum is at most four times the
eighth-power dimension factor and the positive-degree induction sum. -/
theorem pastingEighthSum_le_positive_sum
    (params : Parameters)
    (eps delta gamma zeta : Error)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hgamma0 : 0 ≤ gamma)
    (hzeta0 : 0 ≤ zeta)
    (hratio1 : ((params.d : Error) / (params.q : Error)) ≤ 1)
    (hquarter : zeta ≤
      200 * ((params.m + 1 : ℕ) : Error) *
        (Real.rpow eps (1 / (4 : Error)) +
          Real.rpow delta (1 / (4 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error))
            (1 / (4 : Error)))) :
    pastingEighthSum params eps delta gamma zeta ≤
      4 * Real.rpow (((params.m + 1 : ℕ) : Error)) (1 / (8 : Error)) *
        simplifiedPositiveErrorSum params eps delta gamma := by
  let n : Error := ((params.m + 1 : ℕ) : Error)
  let r : Error := Real.rpow n (1 / (8 : Error))
  let S : Error := simplifiedPositiveErrorSum params eps delta gamma
  have hratio0 : 0 ≤ ((params.d : Error) / (params.q : Error)) := by positivity
  have hN : 1 ≤ n := by
    dsimp [n]
    have hnat : 1 ≤ params.m + 1 := by omega
    exact_mod_cast hnat
  have hr : 1 ≤ r := Real.one_le_rpow hN (by norm_num)
  have hS : 0 ≤ S := by dsimp [S, simplifiedPositiveErrorSum]; positivity
  have heps := eighth_power_le_thirtysecond_power eps heps0 heps1
  have hdelta := eighth_power_le_thirtysecond_power delta hdelta0 hdelta1
  have hratio := eighth_power_le_thirtysecond_power _ hratio0 hratio1
  have hzeta := dilation_eighth_le_positive_sum params eps delta zeta
    heps0 hdelta0 hzeta0 hquarter
  have hbase :
      Real.rpow eps (1 / (8 : Error)) +
        Real.rpow delta (1 / (8 : Error)) +
        Real.rpow gamma (1 / (8 : Error)) +
      Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (8 : Error)) ≤ S := by
    change eps ^ (1 / (8 : Error)) ≤ eps ^ (1 / (32 : Error)) at heps
    change delta ^ (1 / (8 : Error)) ≤ delta ^ (1 / (32 : Error)) at hdelta
    change (((params.d : Error) / (params.q : Error)) ^ (1 / (8 : Error))) ≤
      ((params.d : Error) / (params.q : Error)) ^ (1 / (32 : Error)) at hratio
    dsimp [S, simplifiedPositiveErrorSum]
    linarith
  have hthree : S + 2 * r * S ≤ 4 * r * S := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) hS]
  have hsubsum :
      Real.rpow eps (1 / (32 : Error)) +
        Real.rpow delta (1 / (32 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (32 : Error)) ≤ S := by
    dsimp [S, simplifiedPositiveErrorSum]
    exact le_add_of_nonneg_right (Real.rpow_nonneg hgamma0 _)
  have hzeta' :
      Real.rpow zeta (1 / (8 : Error)) ≤ 2 * r * S := by
    have hfactor : 0 ≤ 2 * r := by positivity
    exact hzeta.trans (mul_le_mul_of_nonneg_left hsubsum hfactor)
  dsimp [pastingEighthSum]
  calc
    Real.rpow eps (1 / (8 : Error)) +
        Real.rpow delta (1 / (8 : Error)) +
        Real.rpow gamma (1 / (8 : Error)) +
        Real.rpow zeta (1 / (8 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error))
          (1 / (8 : Error)) ≤ S + 2 * r * S := by linarith
    _ ≤ 4 * r * S := hthree
    _ = _ := rfl

end MIPStarRE.LDT.MainInductionStep
