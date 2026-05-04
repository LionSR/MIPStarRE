import Mathlib.Analysis.SpecialFunctions.Pow.Real
import MIPStarRE.LDT.Basic.SqrtBounds
import MIPStarRE.LDT.SelfImprovement.Defs

/-!
# Section 9 — Numerical threshold absorptions

Reusable arithmetic threshold lemmas that compare the *natural* paper sums of
errors emitted by the self-improvement producers against the literal
`selfImprovementHelperError` and `selfImprovementError` thresholds used by the
final-field statements (`SelfImprovementFinalFields` in `Statements.lean`).

The helper-stage absorptions formalize the displayed paper inequalities:

* `references/ldt-paper/self_improvement.tex`, lines 438--443 — point
  consistency: `4 √ζ_var ≤ ζ̂`.
* `references/ldt-paper/self_improvement.tex`, lines 595--603 — strong
  self-consistency: `11 √ζ_var + √(2δ) + md/q ≤ ζ̂`.
* `references/ldt-paper/self_improvement.tex`, lines 614--624 — boundedness:
  `3 √δ + 4 √ζ_var ≤ ζ̂`.

The final-stage building block converts the literal
`selfImprovementHelperError` (paper exponent `1/2`) into the literal
`selfImprovementError` threshold (paper exponent `1/32`) for unit-interval
parameters, formalizing the leading exponent-monotonicity step in
`references/ldt-paper/self_improvement.tex`, lines 803--810.

The final projective-residual absorption `ζ̂ + √ζ̂_dataprocess ≤ ζ` is proved
below using the reusable three-term power sum `finalStagePowerSum`. The
remaining orthonormalization-error nesting absorptions
(`6 ζ̂ + 6 ζ̂_ortho ≤ ζ` and `2 ζ̂ + 2 √ζ̂_ortho ≤ ζ`) use the same
bookkeeping pattern and can be added as separate producer-side comparisons.

Blueprint mirrors:

* `blueprint/src/chapter/ch07_self_improvement.tex`, lines 161--168 (point
  consistency), 256--279 (strong self-consistency / boundedness), and
  625--650 (final-stage absorption).
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective

/-! ## Parameter convenience facts -/

private theorem one_le_m_cast (params : Parameters) :
    (1 : Error) ≤ (params.m : Error) := by exact_mod_cast params.hm

private theorem m_cast_nonneg (params : Parameters) :
    (0 : Error) ≤ (params.m : Error) := by positivity

private theorem d_q_ratio_nonneg (params : Parameters) :
    (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
  div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt params.q_cast_pos)

/-- For `m ≥ 1`, `√(24m) ≤ 5m`. -/
private theorem sqrt_24m_le_5m (params : Parameters) :
    Real.sqrt (24 * (params.m : Error)) ≤ 5 * (params.m : Error) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have h5m_nn : (0 : Error) ≤ 5 * (params.m : Error) := by positivity
  refine (Real.sqrt_le_left h5m_nn).mpr ?_
  nlinarith [hmpos, hm1]

/-- For `m ≥ 1`, `√(24 m²) ≤ 5m`. -/
private theorem sqrt_24m_sq_le_5m (params : Parameters) :
    Real.sqrt (24 * ((params.m : Error) ^ (2 : ℕ))) ≤ 5 * (params.m : Error) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have h5m_nn : (0 : Error) ≤ 5 * (params.m : Error) := by positivity
  refine (Real.sqrt_le_left h5m_nn).mpr ?_
  nlinarith [sq_nonneg ((params.m : Error)), hmpos]

private theorem sqrt_100m_le_10m (params : Parameters) :
    Real.sqrt (100 * (params.m : Error)) ≤ 10 * (params.m : Error) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have h10m_nn : (0 : Error) ≤ 10 * (params.m : Error) := by positivity
  refine (Real.sqrt_le_left h10m_nn).mpr ?_
  nlinarith [hmpos, hm1]

private theorem sqrt_10m_le_4m (params : Parameters) :
    Real.sqrt (10 * (params.m : Error)) ≤ 4 * (params.m : Error) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have h4m_nn : (0 : Error) ≤ 4 * (params.m : Error) := by positivity
  refine (Real.sqrt_le_left h4m_nn).mpr ?_
  nlinarith [hmpos, hm1]

private theorem sqrt_400m_le_20m (params : Parameters) :
    Real.sqrt (400 * (params.m : Error)) ≤ 20 * (params.m : Error) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have h20m_nn : (0 : Error) ≤ 20 * (params.m : Error) := by positivity
  refine (Real.sqrt_le_left h20m_nn).mpr ?_
  nlinarith [hmpos, hm1]

private theorem sqrt_960m_le_31m (params : Parameters) :
    Real.sqrt (960 * (params.m : Error)) ≤ 31 * (params.m : Error) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have h31m_nn : (0 : Error) ≤ 31 * (params.m : Error) := by positivity
  refine (Real.sqrt_le_left h31m_nn).mpr ?_
  nlinarith [hmpos, hm1]

/-! ## Subroutine: square-root bound on `globalVarianceOfPointsError`

The paper's central arithmetic step (`self_improvement.tex`, line 441) is

`√(24 m (ε + δ + md/q)) ≤ 20 m (ε^{1/2} + δ^{1/2} + (d/q)^{1/2})`.

We separate the constant `5` from the multipliers `4`/`11`/`3` used downstream
and prove a single reusable bound. -/

/-- Paper-faithful square-root bound on the variance error
(`self_improvement.tex`, lines 440--442). -/
theorem sqrt_selfImprovementVarianceError_le
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    Real.sqrt (selfImprovementVarianceError params eps delta) ≤
      5 * (params.m : Error) *
        (Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error))) := by
  have hmpos : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  -- `selfImprovementVarianceError = 24 * m * (eps + delta + m * (d / q))`
  have hexpand :
      selfImprovementVarianceError params eps delta =
        24 * (params.m : Error) *
          (eps + delta +
            ((params.m : Error) * ((params.d : Error) / (params.q : Error)))) := by
    change 24 * (params.m : Error) *
          (eps + delta + ((params.m : Error) * (params.d : Error) / (params.q : Error))) =
        24 * (params.m : Error) *
          (eps + delta + ((params.m : Error) * ((params.d : Error) / (params.q : Error))))
    rw [mul_div_assoc]
  rw [hexpand]
  have h24m_nn : (0 : Error) ≤ 24 * (params.m : Error) := by positivity
  have hmdq_nn :
      (0 : Error) ≤ (params.m : Error) * ((params.d : Error) / (params.q : Error)) :=
    mul_nonneg hmpos hdq_nonneg
  -- Step 1: √(24m * X) = √(24m) * √X.
  rw [Real.sqrt_mul h24m_nn]
  -- Step 2: √(eps + delta + m*(d/q)) ≤ √eps + √delta + √(m*(d/q)).
  have hstep2 :
      Real.sqrt (eps + delta +
          ((params.m : Error) * ((params.d : Error) / (params.q : Error)))) ≤
        Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.m : Error) *
            ((params.d : Error) / (params.q : Error))) :=
    sqrt_add3_le_add3_sqrt heps hdelta hmdq_nn
  have hsplit_mdq :
      Real.sqrt ((params.m : Error) * ((params.d : Error) / (params.q : Error))) =
        Real.sqrt (params.m : Error) *
          Real.sqrt ((params.d : Error) / (params.q : Error)) :=
    Real.sqrt_mul hmpos _
  -- √(24m) ≤ 5m.
  have hsqrt24m_le : Real.sqrt (24 * (params.m : Error)) ≤ 5 * (params.m : Error) :=
    sqrt_24m_le_5m params
  -- √(24m) * √m = √(24 m²) ≤ 5m.
  have hsplit_24m_m :
      Real.sqrt (24 * (params.m : Error)) * Real.sqrt (params.m : Error) =
        Real.sqrt (24 * ((params.m : Error) ^ (2 : ℕ))) := by
    rw [← Real.sqrt_mul h24m_nn]
    congr 1; ring
  have hsqrt24m_m_le :
      Real.sqrt (24 * (params.m : Error)) * Real.sqrt (params.m : Error) ≤
        5 * (params.m : Error) := by
    rw [hsplit_24m_m]
    exact sqrt_24m_sq_le_5m params
  have hsqrt24m_nn : (0 : Error) ≤ Real.sqrt (24 * (params.m : Error)) :=
    Real.sqrt_nonneg _
  calc
    Real.sqrt (24 * (params.m : Error)) *
        Real.sqrt (eps + delta +
          ((params.m : Error) * ((params.d : Error) / (params.q : Error))))
        ≤ Real.sqrt (24 * (params.m : Error)) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.m : Error) *
                ((params.d : Error) / (params.q : Error)))) :=
          mul_le_mul_of_nonneg_left hstep2 hsqrt24m_nn
    _ = Real.sqrt (24 * (params.m : Error)) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt (params.m : Error) *
              Real.sqrt ((params.d : Error) / (params.q : Error))) := by
          rw [hsplit_mdq]
    _ = Real.sqrt (24 * (params.m : Error)) * Real.sqrt eps +
          Real.sqrt (24 * (params.m : Error)) * Real.sqrt delta +
          (Real.sqrt (24 * (params.m : Error)) * Real.sqrt (params.m : Error)) *
            Real.sqrt ((params.d : Error) / (params.q : Error)) := by ring
    _ ≤ 5 * (params.m : Error) * Real.sqrt eps +
          5 * (params.m : Error) * Real.sqrt delta +
          5 * (params.m : Error) *
            Real.sqrt ((params.d : Error) / (params.q : Error)) := by
          have h1 :
              Real.sqrt (24 * (params.m : Error)) * Real.sqrt eps ≤
                5 * (params.m : Error) * Real.sqrt eps :=
            mul_le_mul_of_nonneg_right hsqrt24m_le (Real.sqrt_nonneg _)
          have h2 :
              Real.sqrt (24 * (params.m : Error)) * Real.sqrt delta ≤
                5 * (params.m : Error) * Real.sqrt delta :=
            mul_le_mul_of_nonneg_right hsqrt24m_le (Real.sqrt_nonneg _)
          have h3 :
              (Real.sqrt (24 * (params.m : Error)) *
                  Real.sqrt (params.m : Error)) *
                  Real.sqrt ((params.d : Error) / (params.q : Error)) ≤
                5 * (params.m : Error) *
                  Real.sqrt ((params.d : Error) / (params.q : Error)) :=
            mul_le_mul_of_nonneg_right hsqrt24m_m_le (Real.sqrt_nonneg _)
          linarith
    _ = 5 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring

private theorem sum_sqrt_eq_sum_rpow_half
    (eps delta dq : Error) :
    Real.sqrt eps + Real.sqrt delta + Real.sqrt dq =
      Real.rpow eps (1 / (2 : Error)) + Real.rpow delta (1 / (2 : Error)) +
        Real.rpow dq (1 / (2 : Error)) := by
  simp [Real.sqrt_eq_rpow, Real.rpow_eq_pow]

/-- Expansion of the helper-stage self-improvement error into the square-root
sum used in the paper.

This form is often the convenient one for the helper-stage absorptions: it
identifies `selfImprovementHelperError` with
`100 m (√ε + √δ + √(d/q))`, rather than requiring each proof to unfold the
definition and convert the three `rpow` terms separately. -/
theorem selfImprovementHelperError_eq
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementHelperError params eps delta =
      100 * (params.m : Error) *
        (Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error))) := by
  rw [selfImprovementHelperError,
    sum_sqrt_eq_sum_rpow_half eps delta ((params.d : Error) / (params.q : Error))]

/-- The helper-stage threshold is nonnegative for nonnegative `eps` and `delta`.

This is the basic positivity fact reused by the helper-stage absorption wrappers
and by the final-stage comparison with `selfImprovementError`. -/
theorem selfImprovementHelperError_nonneg
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (_heps : 0 ≤ eps) (_hdelta : 0 ≤ delta) :
    0 ≤ selfImprovementHelperError params eps delta := by
  rw [selfImprovementHelperError_eq]
  have hcoef_nn : (0 : Error) ≤ 100 * (params.m : Error) := by positivity
  have heps_sqrt_nn : (0 : Error) ≤ Real.sqrt eps := by
    exact Real.sqrt_nonneg eps
  have hdelta_sqrt_nn : (0 : Error) ≤ Real.sqrt delta := by
    exact Real.sqrt_nonneg delta
  have hdq_sqrt_nn :
      (0 : Error) ≤ Real.sqrt ((params.d : Error) / (params.q : Error)) := by
    exact Real.sqrt_nonneg _
  have hsum_nn :
      (0 : Error) ≤ Real.sqrt eps + Real.sqrt delta +
        Real.sqrt ((params.d : Error) / (params.q : Error)) := by
    exact add_nonneg (add_nonneg heps_sqrt_nn hdelta_sqrt_nn) hdq_sqrt_nn
  exact mul_nonneg hcoef_nn hsum_nn

/-- Helper-stage point-consistency absorption (`self_improvement.tex`,
lines 438--443).

`4 √ζ_variance ≤ ζ̂`. -/
theorem helper_point_consistency_error_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    4 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
      selfImprovementHelperError params eps delta := by
  have hsqrtbound :=
    sqrt_selfImprovementVarianceError_le params eps delta heps hdelta
  have hmnonneg : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hsum_nonneg :
      (0 : Error) ≤ Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by positivity
  rw [selfImprovementHelperError_eq]
  calc
    4 * Real.sqrt (selfImprovementVarianceError params eps delta)
        ≤ 4 * (5 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error)))) :=
          mul_le_mul_of_nonneg_left hsqrtbound (by norm_num)
    _ = 20 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring
    _ ≤ 100 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
          have hcoef : (20 : Error) * (params.m : Error) ≤ 100 * (params.m : Error) := by
            nlinarith [hmnonneg]
          exact mul_le_mul_of_nonneg_right hcoef hsum_nonneg

/-- Helper-stage strong-self-consistency absorption (`self_improvement.tex`,
lines 595--603).

`11 √ζ_variance + √(2δ) + md/q ≤ ζ̂`. -/
theorem helper_strong_self_consistency_error_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
        Real.sqrt (2 * delta) +
        ((params.m : Error) * (params.d : Error) / (params.q : Error)) ≤
      selfImprovementHelperError params eps delta := by
  have hmnonneg : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have hqpos : (0 : Error) < (params.q : Error) := params.q_cast_pos
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    (div_le_one hqpos).mpr hd_le_q
  have hsqrtbound :=
    sqrt_selfImprovementVarianceError_le params eps delta heps hdelta
  -- `√(2δ) ≤ 2 √δ`, since `√2 ≤ 2`.
  have hsqrt2_le_2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.mul_self_sqrt (by norm_num : (0 : Error) ≤ 2),
      Real.sqrt_nonneg (2 : Error)]
  have hsqrt2delta_le :
      Real.sqrt (2 * delta) ≤ 2 * Real.sqrt delta := by
    rw [Real.sqrt_mul (by norm_num : (0 : Error) ≤ 2)]
    exact mul_le_mul_of_nonneg_right hsqrt2_le_2 (Real.sqrt_nonneg _)
  -- `m * d / q = m * (d / q) ≤ m * √(d/q)` since `d/q ∈ [0, 1]`.
  have hdq_le_sqrt_dq :
      ((params.d : Error) / (params.q : Error)) ≤
        Real.sqrt ((params.d : Error) / (params.q : Error)) := by
    have hsqrtnn :
        (0 : Error) ≤ Real.sqrt ((params.d : Error) / (params.q : Error)) :=
      Real.sqrt_nonneg _
    have hsqrt_self :
        Real.sqrt ((params.d : Error) / (params.q : Error)) *
          Real.sqrt ((params.d : Error) / (params.q : Error)) =
          (params.d : Error) / (params.q : Error) :=
      Real.mul_self_sqrt hdq_nonneg
    have hsqrt_le_one :
        Real.sqrt ((params.d : Error) / (params.q : Error)) ≤ 1 :=
      Real.sqrt_le_one.mpr hdq_le_one
    nlinarith [hsqrtnn, hsqrt_self, hsqrt_le_one, hdq_nonneg]
  have hmd_q_eq :
      (params.m : Error) * (params.d : Error) / (params.q : Error) =
        (params.m : Error) * ((params.d : Error) / (params.q : Error)) :=
    mul_div_assoc _ _ _
  have hmd_q_le_msqrt :
      (params.m : Error) * (params.d : Error) / (params.q : Error) ≤
        (params.m : Error) *
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by
    rw [hmd_q_eq]
    exact mul_le_mul_of_nonneg_left hdq_le_sqrt_dq hmnonneg
  -- Components of the sum-of-roots `s`.
  have hsum_nonneg :
      (0 : Error) ≤ Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by positivity
  have hsqrt_eps_nn : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg _
  have hsqrt_delta_nn : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrt_dq_nn : 0 ≤ Real.sqrt ((params.d : Error) / (params.q : Error)) :=
    Real.sqrt_nonneg _
  have hsqrt_delta_le_sum : Real.sqrt delta ≤
      Real.sqrt eps + Real.sqrt delta +
        Real.sqrt ((params.d : Error) / (params.q : Error)) := by linarith
  have hsqrt_dq_le_sum :
      Real.sqrt ((params.d : Error) / (params.q : Error)) ≤
        Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by linarith
  -- 11 √varE ≤ 55 m * sum.
  have h11 :
      11 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
        55 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
    calc
      11 * Real.sqrt (selfImprovementVarianceError params eps delta)
          ≤ 11 * (5 * (params.m : Error) *
              (Real.sqrt eps + Real.sqrt delta +
                Real.sqrt ((params.d : Error) / (params.q : Error)))) :=
            mul_le_mul_of_nonneg_left hsqrtbound (by norm_num)
      _ = 55 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring
  -- √(2δ) ≤ 2m * sum.
  have h2sqrt :
      Real.sqrt (2 * delta) ≤ 2 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
    have h2coef : (2 : Error) ≤ 2 * (params.m : Error) := by nlinarith [hm1]
    have h2m_nn : (0 : Error) ≤ 2 * (params.m : Error) := by nlinarith [hmnonneg]
    calc
      Real.sqrt (2 * delta)
          ≤ 2 * Real.sqrt delta := hsqrt2delta_le
      _ ≤ 2 * (params.m : Error) * Real.sqrt delta :=
          mul_le_mul_of_nonneg_right h2coef hsqrt_delta_nn
      _ ≤ 2 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) :=
          mul_le_mul_of_nonneg_left hsqrt_delta_le_sum h2m_nn
  -- m * d / q ≤ m * sum.
  have hmd_q_le_msum :
      (params.m : Error) * (params.d : Error) / (params.q : Error) ≤
        (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
    calc
      (params.m : Error) * (params.d : Error) / (params.q : Error)
          ≤ (params.m : Error) *
              Real.sqrt ((params.d : Error) / (params.q : Error)) := hmd_q_le_msqrt
      _ ≤ (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) :=
          mul_le_mul_of_nonneg_left hsqrt_dq_le_sum hmnonneg
  rw [selfImprovementHelperError_eq]
  calc
    11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
        Real.sqrt (2 * delta) +
        ((params.m : Error) * (params.d : Error) / (params.q : Error))
        ≤ 55 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) +
          2 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) +
          (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) := by
        linarith
    _ = 58 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring
    _ ≤ 100 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
        have hcoef : (58 : Error) * (params.m : Error) ≤ 100 * (params.m : Error) := by
          nlinarith [hmnonneg]
        exact mul_le_mul_of_nonneg_right hcoef hsum_nonneg

/-- Helper-stage boundedness absorption (`self_improvement.tex`, lines
614--624).

`3 √δ + 4 √ζ_variance ≤ ζ̂`. -/
theorem helper_boundedness_error_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    3 * Real.sqrt delta + 4 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
      selfImprovementHelperError params eps delta := by
  have hmnonneg : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
  have hm1 : (1 : Error) ≤ (params.m : Error) := one_le_m_cast params
  have hsqrtbound :=
    sqrt_selfImprovementVarianceError_le params eps delta heps hdelta
  have hsqrt_eps_nn : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg _
  have hsqrt_delta_nn : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg _
  have hsqrt_dq_nn : 0 ≤ Real.sqrt ((params.d : Error) / (params.q : Error)) :=
    Real.sqrt_nonneg _
  have hsum_nonneg :
      (0 : Error) ≤ Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by positivity
  have hsqrt_delta_le_sum :
      Real.sqrt delta ≤
        Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error)) := by linarith
  -- 3 √δ ≤ 3m * sum.
  have h3sqrt_delta :
      3 * Real.sqrt delta ≤ 3 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
    have h3coef : (3 : Error) ≤ 3 * (params.m : Error) := by nlinarith [hm1]
    have h3m_nn : (0 : Error) ≤ 3 * (params.m : Error) := by nlinarith [hmnonneg]
    calc
      3 * Real.sqrt delta
          ≤ 3 * (params.m : Error) * Real.sqrt delta :=
            mul_le_mul_of_nonneg_right h3coef hsqrt_delta_nn
      _ ≤ 3 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) :=
            mul_le_mul_of_nonneg_left hsqrt_delta_le_sum h3m_nn
  -- 4 √varE ≤ 20 m * sum.
  have h4sqrt :
      4 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
        20 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
    calc
      4 * Real.sqrt (selfImprovementVarianceError params eps delta)
          ≤ 4 * (5 * (params.m : Error) *
              (Real.sqrt eps + Real.sqrt delta +
                Real.sqrt ((params.d : Error) / (params.q : Error)))) :=
            mul_le_mul_of_nonneg_left hsqrtbound (by norm_num)
      _ = 20 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring
  rw [selfImprovementHelperError_eq]
  calc
    3 * Real.sqrt delta + 4 * Real.sqrt (selfImprovementVarianceError params eps delta)
        ≤ 3 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) +
          20 * (params.m : Error) *
            (Real.sqrt eps + Real.sqrt delta +
              Real.sqrt ((params.d : Error) / (params.q : Error))) := by linarith
    _ = 23 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by ring
    _ ≤ 100 * (params.m : Error) *
          (Real.sqrt eps + Real.sqrt delta +
            Real.sqrt ((params.d : Error) / (params.q : Error))) := by
        have hcoef : (23 : Error) * (params.m : Error) ≤ 100 * (params.m : Error) := by
          nlinarith [hmnonneg]
        exact mul_le_mul_of_nonneg_right hcoef hsum_nonneg

/-- Helper-stage completeness absorption (`self_improvement.tex`, lines
403--414).

The loss `3 √δ` from the Cauchy--Schwarz comparison is bounded by the helper
threshold `ζ̂`. -/
theorem helper_completeness_error_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    3 * Real.sqrt delta ≤ selfImprovementHelperError params eps delta := by
  have hvariance_nonneg :
      0 ≤ 4 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
    positivity
  calc
    3 * Real.sqrt delta
        ≤ 3 * Real.sqrt delta +
            4 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
          linarith
    _ ≤ selfImprovementHelperError params eps delta :=
          helper_boundedness_error_le_selfImprovementHelperError params eps delta
            heps hdelta

/-! ## Final-stage threshold: `30 ζ̂ ≤ ζ`

For `ε, δ, d/q ∈ [0, 1]`, the helper-stage error is dominated by
`selfImprovementError / 30`. This is the exponent-monotonicity step in the
paper's chained absorption (`self_improvement.tex`, lines 803--810): for
unit-interval `x` and `0 ≤ z ≤ y`, `x^y ≤ x^z`. -/

/-- The three-term power sum used in the final-stage self-improvement threshold
bookkeeping.

For exponent `p`, this is the Lean counterpart of
`ε^p + δ^p + (d/q)^p`. Keeping this expression named makes the nested
absorptions in `self_improvement.tex`, lines 772--810, insensitive to future
constant adjustments. -/
noncomputable def finalStagePowerSum (params : Parameters)
    (eps delta p : Error) : Error :=
  Real.rpow eps p + Real.rpow delta p +
    Real.rpow ((params.d : Error) / (params.q : Error)) p

private theorem finalStagePowerSum_nonneg
    (params : Parameters) (eps delta p : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    0 ≤ finalStagePowerSum params eps delta p := by
  unfold finalStagePowerSum
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  exact add_nonneg
    (add_nonneg (Real.rpow_nonneg heps _) (Real.rpow_nonneg hdelta _))
    (Real.rpow_nonneg hdq_nonneg _)

private theorem finalStagePowerSum_le_of_exponent_ge
    (params : Parameters) (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1)
    {pLarge pSmall : Error} (hpSmall_nonneg : 0 ≤ pSmall)
    (hpSmall_le_pLarge : pSmall ≤ pLarge) :
    finalStagePowerSum params eps delta pLarge ≤
      finalStagePowerSum params eps delta pSmall := by
  unfold finalStagePowerSum
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact Real.rpow_le_rpow_of_exponent_ge' heps heps_le_one hpSmall_nonneg
      hpSmall_le_pLarge
  · exact Real.rpow_le_rpow_of_exponent_ge' hdelta hdelta_le_one hpSmall_nonneg
      hpSmall_le_pLarge
  · exact Real.rpow_le_rpow_of_exponent_ge' hdq_nonneg hdq_le_one hpSmall_nonneg
      hpSmall_le_pLarge

private theorem sqrt_rpow_eq_rpow_half {x p : Error} (hx : 0 ≤ x) :
    Real.sqrt (Real.rpow x p) = Real.rpow x (p / 2) := by
  rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (Real.rpow x p) (1 / (2 : Error)) = Real.rpow x (p * (1 / 2)) := by
      exact (Real.rpow_mul hx p (1 / (2 : Error))).symm
    _ = Real.rpow x (p / 2) := by ring_nf

private theorem sqrt_finalStagePowerSum_le
    (params : Parameters) (eps delta p : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    Real.sqrt (finalStagePowerSum params eps delta p) ≤
      finalStagePowerSum params eps delta (p / 2) := by
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  unfold finalStagePowerSum
  calc
    Real.sqrt (Real.rpow eps p + Real.rpow delta p +
        Real.rpow ((params.d : Error) / (params.q : Error)) p)
        ≤ Real.sqrt (Real.rpow eps p) + Real.sqrt (Real.rpow delta p) +
          Real.sqrt (Real.rpow ((params.d : Error) / (params.q : Error)) p) :=
      sqrt_add3_le_add3_sqrt (Real.rpow_nonneg heps _) (Real.rpow_nonneg hdelta _)
        (Real.rpow_nonneg hdq_nonneg _)
    _ = Real.rpow eps (p / 2) + Real.rpow delta (p / 2) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (p / 2) := by
      rw [sqrt_rpow_eq_rpow_half heps, sqrt_rpow_eq_rpow_half hdelta,
        sqrt_rpow_eq_rpow_half hdq_nonneg]

private theorem selfImprovementHelperError_eq_finalStagePowerSum
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementHelperError params eps delta =
      100 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (2 : Error)) := by
  rfl

private theorem selfImprovementError_eq_finalStagePowerSum
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementError params eps delta =
      3000 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
  rfl

private theorem sqrt_selfImprovementHelperError_le_ten_m_powerSum_quarter
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    Real.sqrt (selfImprovementHelperError params eps delta) ≤
      10 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (4 : Error)) := by
  have h100m_nn : (0 : Error) ≤ 100 * (params.m : Error) := by positivity
  have hsqrt100m := sqrt_100m_le_10m params
  have hsqrt_sum :=
    sqrt_finalStagePowerSum_le params eps delta (1 / (2 : Error)) heps hdelta
  have h10m_nn : (0 : Error) ≤ 10 * (params.m : Error) := by positivity
  rw [selfImprovementHelperError_eq_finalStagePowerSum]
  calc
    Real.sqrt (100 * (params.m : Error) *
        finalStagePowerSum params eps delta (1 / (2 : Error)))
        = Real.sqrt (100 * (params.m : Error)) *
          Real.sqrt (finalStagePowerSum params eps delta (1 / (2 : Error))) := by
          rw [Real.sqrt_mul h100m_nn]
    _ ≤ (10 * (params.m : Error)) *
          finalStagePowerSum params eps delta (1 / (4 : Error)) := by
          calc
            Real.sqrt (100 * (params.m : Error)) *
                Real.sqrt (finalStagePowerSum params eps delta (1 / (2 : Error)))
                ≤ (10 * (params.m : Error)) *
                    Real.sqrt (finalStagePowerSum params eps delta (1 / (2 : Error))) :=
                  mul_le_mul_of_nonneg_right hsqrt100m (Real.sqrt_nonneg _)
            _ ≤ (10 * (params.m : Error)) *
                  finalStagePowerSum params eps delta (1 / (4 : Error)) := by
                  convert mul_le_mul_of_nonneg_left hsqrt_sum h10m_nn using 2
                  ring_nf

private theorem rpow_quarter_eq_sqrt_sqrt {x : Error} (hx : 0 ≤ x) :
    Real.rpow x (1 / (4 : Error)) = Real.sqrt (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  calc
    Real.rpow x (1 / (4 : Error)) = Real.rpow x ((1 / (2 : Error)) * (1 / 2)) := by
      congr 1
      ring
    _ = Real.rpow (Real.rpow x (1 / (2 : Error))) (1 / (2 : Error)) := by
      exact Real.rpow_mul hx (1 / (2 : Error)) (1 / (2 : Error))

private theorem selfImprovementOrthogonalizationError_le_four_hundred_m_powerSum_eighth
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    selfImprovementOrthogonalizationError params eps delta ≤
      400 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (8 : Error)) := by
  have hhelper_nn : 0 ≤ selfImprovementHelperError params eps delta :=
    selfImprovementHelperError_nonneg params eps delta heps hdelta
  have hsqrt_helper :=
    sqrt_selfImprovementHelperError_le_ten_m_powerSum_quarter params eps delta heps hdelta
  have hsqrt_mS :
      Real.sqrt (10 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (4 : Error))) ≤
        4 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (8 : Error)) := by
    have h10m_nn : (0 : Error) ≤ 10 * (params.m : Error) := by positivity
    have hsqrt10m := sqrt_10m_le_4m params
    have hsqrt_sum :=
      sqrt_finalStagePowerSum_le params eps delta (1 / (4 : Error)) heps hdelta
    have h4m_nn : (0 : Error) ≤ 4 * (params.m : Error) := by positivity
    calc
      Real.sqrt (10 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (4 : Error)))
          = Real.sqrt (10 * (params.m : Error)) *
            Real.sqrt (finalStagePowerSum params eps delta (1 / (4 : Error))) := by
            rw [Real.sqrt_mul h10m_nn]
      _ ≤ (4 * (params.m : Error)) *
            finalStagePowerSum params eps delta (1 / (8 : Error)) := by
            calc
              Real.sqrt (10 * (params.m : Error)) *
                  Real.sqrt (finalStagePowerSum params eps delta (1 / (4 : Error)))
                  ≤ (4 * (params.m : Error)) *
                      Real.sqrt (finalStagePowerSum params eps delta (1 / (4 : Error))) :=
                    mul_le_mul_of_nonneg_right hsqrt10m (Real.sqrt_nonneg _)
              _ ≤ (4 * (params.m : Error)) *
                    finalStagePowerSum params eps delta (1 / (8 : Error)) := by
                    convert mul_le_mul_of_nonneg_left hsqrt_sum h4m_nn using 2
                    ring_nf
  unfold selfImprovementOrthogonalizationError orthonormalizationError
  rw [rpow_quarter_eq_sqrt_sqrt hhelper_nn]
  calc
    100 * Real.sqrt (Real.sqrt (selfImprovementHelperError params eps delta))
        ≤ 100 * Real.sqrt
            (10 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (4 : Error))) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsqrt_helper) (by norm_num)
    _ ≤ 100 * (4 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (8 : Error))) :=
        mul_le_mul_of_nonneg_left hsqrt_mS (by norm_num)
    _ = 400 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (8 : Error)) := by ring

private theorem sqrt_selfImprovementOrthogonalizationError_le_twenty_m_powerSum_sixteenth
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
      20 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (16 : Error)) := by
  have horth :=
    selfImprovementOrthogonalizationError_le_four_hundred_m_powerSum_eighth
      params eps delta heps hdelta
  have h400m_nn : (0 : Error) ≤ 400 * (params.m : Error) := by positivity
  have hsqrt400m := sqrt_400m_le_20m params
  have hsqrt_sum :=
    sqrt_finalStagePowerSum_le params eps delta (1 / (8 : Error)) heps hdelta
  have h20m_nn : (0 : Error) ≤ 20 * (params.m : Error) := by positivity
  calc
    Real.sqrt (selfImprovementOrthogonalizationError params eps delta)
        ≤ Real.sqrt (400 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (8 : Error))) :=
          Real.sqrt_le_sqrt horth
    _ = Real.sqrt (400 * (params.m : Error)) *
          Real.sqrt (finalStagePowerSum params eps delta (1 / (8 : Error))) := by
          rw [Real.sqrt_mul h400m_nn]
    _ ≤ (20 * (params.m : Error)) *
          finalStagePowerSum params eps delta (1 / (16 : Error)) := by
          calc
            Real.sqrt (400 * (params.m : Error)) *
                Real.sqrt (finalStagePowerSum params eps delta (1 / (8 : Error)))
                ≤ (20 * (params.m : Error)) *
                    Real.sqrt (finalStagePowerSum params eps delta (1 / (8 : Error))) :=
                  mul_le_mul_of_nonneg_right hsqrt400m (Real.sqrt_nonneg _)
            _ ≤ (20 * (params.m : Error)) *
                  finalStagePowerSum params eps delta (1 / (16 : Error)) := by
                  convert mul_le_mul_of_nonneg_left hsqrt_sum h20m_nn using 2
                  ring_nf

private theorem selfImprovementDataProcessingError_le_nine_sixty_m_powerSum_sixteenth
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    selfImprovementDataProcessingError params eps delta ≤
      960 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (16 : Error)) := by
  have hhelper_mono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (16 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hhelper :
      selfImprovementHelperError params eps delta ≤
        100 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (16 : Error)) := by
    rw [selfImprovementHelperError_eq_finalStagePowerSum]
    exact mul_le_mul_of_nonneg_left hhelper_mono (by positivity)
  have hsqrt_orth :=
    sqrt_selfImprovementOrthogonalizationError_le_twenty_m_powerSum_sixteenth
      params eps delta heps hdelta
  unfold selfImprovementDataProcessingError
  calc
    8 * selfImprovementHelperError params eps delta +
        8 * Real.rpow (selfImprovementOrthogonalizationError params eps delta)
          (1 / (2 : Error))
        = 8 * selfImprovementHelperError params eps delta +
            8 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
          simp [Real.sqrt_eq_rpow, Real.rpow_eq_pow]
    _ ≤ 8 * (100 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (16 : Error))) +
          8 * (20 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (16 : Error))) := by
          gcongr
    _ = 960 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (16 : Error)) := by ring

private theorem sqrt_selfImprovementDataProcessingError_le_thirty_one_m_powerSum_thirtysecond
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
      31 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
  have hdata :=
    selfImprovementDataProcessingError_le_nine_sixty_m_powerSum_sixteenth
      params eps delta heps heps_le_one hdelta hdelta_le_one hdq_le_one
  have h960m_nn : (0 : Error) ≤ 960 * (params.m : Error) := by positivity
  have hsqrt960m := sqrt_960m_le_31m params
  have hsqrt_sum :=
    sqrt_finalStagePowerSum_le params eps delta (1 / (16 : Error)) heps hdelta
  have h31m_nn : (0 : Error) ≤ 31 * (params.m : Error) := by positivity
  calc
    Real.sqrt (selfImprovementDataProcessingError params eps delta)
        ≤ Real.sqrt (960 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (16 : Error))) :=
          Real.sqrt_le_sqrt hdata
    _ = Real.sqrt (960 * (params.m : Error)) *
          Real.sqrt (finalStagePowerSum params eps delta (1 / (16 : Error))) := by
          rw [Real.sqrt_mul h960m_nn]
    _ ≤ (31 * (params.m : Error)) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
          calc
            Real.sqrt (960 * (params.m : Error)) *
                Real.sqrt (finalStagePowerSum params eps delta (1 / (16 : Error)))
                ≤ (31 * (params.m : Error)) *
                    Real.sqrt (finalStagePowerSum params eps delta (1 / (16 : Error))) :=
                  mul_le_mul_of_nonneg_right hsqrt960m (Real.sqrt_nonneg _)
            _ ≤ (31 * (params.m : Error)) *
                  finalStagePowerSum params eps delta (1 / (32 : Error)) := by
                  convert mul_le_mul_of_nonneg_left hsqrt_sum h31m_nn using 2
                  ring_nf

/-- Final projective-residual threshold absorption (`self_improvement.tex`,
lines 803--810).

The natural error emitted by the projective residual producer is
`ζ̂ + √ζ̂_dataprocess`. Under the standard unit-interval hypotheses for
`ε`, `δ`, and `d/q`, this theorem absorbs that natural error into the literal
`selfImprovementError` threshold used by `SelfImprovementConclusion`. -/
theorem final_fields_projective_residual_error_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
      selfImprovementError params eps delta := by
  have hqpos : (0 : Error) < (params.q : Error) := params.q_cast_pos
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    (div_le_one hqpos).mpr hd_le_q
  have hhelper_mono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hhelper :
      selfImprovementHelperError params eps delta ≤
        100 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    rw [selfImprovementHelperError_eq_finalStagePowerSum]
    exact mul_le_mul_of_nonneg_left hhelper_mono (by positivity)
  have hdata_sqrt :=
    sqrt_selfImprovementDataProcessingError_le_thirty_one_m_powerSum_thirtysecond
      params eps delta heps heps_le_one hdelta hdelta_le_one hdq_le_one
  have hsum32_nn :
      0 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_nonneg params eps delta (1 / (32 : Error)) heps hdelta
  have hcoef :
      131 * (params.m : Error) ≤ 3000 * (params.m : Error) := by
    nlinarith [m_cast_nonneg params]
  calc
    selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta)
        ≤ 100 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (32 : Error)) +
          31 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (32 : Error)) := by
          linarith
    _ = 131 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by ring
    _ ≤ 3000 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) :=
        mul_le_mul_of_nonneg_right hcoef hsum32_nn
    _ = selfImprovementError params eps delta := by
      rw [selfImprovementError_eq_finalStagePowerSum]

/-- Final completeness threshold absorption (`self_improvement.tex`,
lines 803--810).

The natural error emitted by the projective completeness transport is
`2ζ̂ + 2 sqrt ζ̂_ortho`. Under the standard unit-interval hypotheses for
`ε`, `δ`, and `d/q`, this theorem absorbs that natural error into the literal
`selfImprovementError` threshold used by `SelfImprovementFinalFields`. -/
theorem final_fields_completeness_error_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    2 * selfImprovementHelperError params eps delta +
        2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
      selfImprovementError params eps delta := by
  have hqpos : (0 : Error) < (params.q : Error) := params.q_cast_pos
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    (div_le_one hqpos).mpr hd_le_q
  have hhelper_mono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hsqrt_orth_mono :
      finalStagePowerSum params eps delta (1 / (16 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hhelper :
      selfImprovementHelperError params eps delta ≤
        100 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    rw [selfImprovementHelperError_eq_finalStagePowerSum]
    exact mul_le_mul_of_nonneg_left hhelper_mono (by positivity)
  have hsqrt_orth :
      Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
        20 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    have hsqrt16 :=
      sqrt_selfImprovementOrthogonalizationError_le_twenty_m_powerSum_sixteenth
        params eps delta heps hdelta
    exact hsqrt16.trans
      (mul_le_mul_of_nonneg_left hsqrt_orth_mono (by positivity))
  have hm_nonneg : 0 ≤ (params.m : Error) := m_cast_nonneg params
  have hsum32_nonneg :
      0 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_nonneg params eps delta (1 / (32 : Error)) heps hdelta
  have hnatural :
      2 * selfImprovementHelperError params eps delta +
          2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
        3000 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    nlinarith
  calc
    2 * selfImprovementHelperError params eps delta +
        2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta)
        ≤ 3000 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (32 : Error)) := hnatural
    _ = selfImprovementError params eps delta := by
      rw [selfImprovementError_eq_finalStagePowerSum]

/-- Final self-closeness threshold absorption (`self_improvement.tex`,
lines 803--810).

The natural error emitted by the projective self-closeness transport is
`3 * (ζ̂_ortho + 2ζ̂ + ζ̂_ortho)`. Under the standard unit-interval hypotheses
for `ε`, `δ`, and `d/q`, this theorem absorbs that natural error into the
literal `selfImprovementError` threshold used by `SelfImprovementFinalFields`.
-/
theorem final_fields_self_closeness_error_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    3 * (selfImprovementOrthogonalizationError params eps delta +
        2 * selfImprovementHelperError params eps delta +
        selfImprovementOrthogonalizationError params eps delta) ≤
      selfImprovementError params eps delta := by
  have hqpos : (0 : Error) < (params.q : Error) := params.q_cast_pos
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    (div_le_one hqpos).mpr hd_le_q
  have horth_mono :
      finalStagePowerSum params eps delta (1 / (8 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have hhelper_mono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have horth :
      selfImprovementOrthogonalizationError params eps delta ≤
        400 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    have horth8 :=
      selfImprovementOrthogonalizationError_le_four_hundred_m_powerSum_eighth
        params eps delta heps hdelta
    exact horth8.trans
      (mul_le_mul_of_nonneg_left horth_mono (by positivity))
  have hhelper :
      selfImprovementHelperError params eps delta ≤
        100 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    rw [selfImprovementHelperError_eq_finalStagePowerSum]
    exact mul_le_mul_of_nonneg_left hhelper_mono (by positivity)
  have hnatural :
      3 * (selfImprovementOrthogonalizationError params eps delta +
          2 * selfImprovementHelperError params eps delta +
          selfImprovementOrthogonalizationError params eps delta) ≤
        3000 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    nlinarith
  calc
    3 * (selfImprovementOrthogonalizationError params eps delta +
        2 * selfImprovementHelperError params eps delta +
        selfImprovementOrthogonalizationError params eps delta)
        ≤ 3000 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (32 : Error)) := hnatural
    _ = selfImprovementError params eps delta := by
      rw [selfImprovementError_eq_finalStagePowerSum]

/-- `30 * selfImprovementHelperError ≤ selfImprovementError` for unit-interval
parameters.

This formalizes the leading exponent-monotonicity step of the paper's chained
absorption in `self_improvement.tex`, lines 803--810. It is the foundational
final-stage threshold from which the producer-side projective-output
absorptions are derived. -/
theorem thirty_selfImprovementHelperError_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    30 * selfImprovementHelperError params eps delta ≤
      selfImprovementError params eps delta := by
  have hqpos : (0 : Error) < (params.q : Error) := params.q_cast_pos
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    (div_le_one hqpos).mpr hd_le_q
  have hmono :
      finalStagePowerSum params eps delta (1 / (2 : Error)) ≤
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_le_of_exponent_ge params eps delta heps heps_le_one hdelta
      hdelta_le_one hdq_le_one (by norm_num) (by norm_num)
  have h3000m_nn : (0 : Error) ≤ 3000 * (params.m : Error) := by positivity
  -- Both sides expand to `3000 m * sum_p` for matching exponents `p`.
  rw [selfImprovementHelperError_eq_finalStagePowerSum,
    selfImprovementError_eq_finalStagePowerSum]
  calc
    30 *
        (100 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (2 : Error)))
        =
      3000 * (params.m : Error) *
        finalStagePowerSum params eps delta (1 / (2 : Error)) := by
            ring
    _ ≤
      3000 * (params.m : Error) *
        finalStagePowerSum params eps delta (1 / (32 : Error)) :=
        mul_le_mul_of_nonneg_left hmono h3000m_nn

/-- A direct corollary of `thirty_selfImprovementHelperError_le_selfImprovementError`:
the literal helper threshold is itself dominated by `selfImprovementError`. -/
theorem selfImprovementHelperError_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    selfImprovementHelperError params eps delta ≤
      selfImprovementError params eps delta := by
  have h30 :=
    thirty_selfImprovementHelperError_le_selfImprovementError params eps delta
      heps heps_le_one hdelta hdelta_le_one hd_le_q
  have hhelper_nn : 0 ≤ selfImprovementHelperError params eps delta :=
    selfImprovementHelperError_nonneg params eps delta heps hdelta
  linarith

end MIPStarRE.LDT.SelfImprovement
