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

The orthonormalization-error nesting absorptions
(`6 ζ̂ + 6 ζ̂_ortho ≤ ζ`, `2 ζ̂ + 2 √ζ̂_ortho ≤ ζ`,
`ζ̂ + √ζ̂_dataprocess ≤ ζ`) require the rpow-subadditivity chain at
`self_improvement.tex`, lines 772--810, and are intentionally left to a
follow-up so this file ships without proof-evasion or new sorrys.

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

private theorem selfImprovementHelperError_eq
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementHelperError params eps delta =
      100 * (params.m : Error) *
        (Real.sqrt eps + Real.sqrt delta +
          Real.sqrt ((params.d : Error) / (params.q : Error))) := by
  rw [selfImprovementHelperError,
    sum_sqrt_eq_sum_rpow_half eps delta ((params.d : Error) / (params.q : Error))]

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

/-! ## Final-stage threshold: `30 ζ̂ ≤ ζ`

For `ε, δ, d/q ∈ [0, 1]`, the helper-stage error is dominated by
`selfImprovementError / 30`. This is the exponent-monotonicity step in the
paper's chained absorption (`self_improvement.tex`, lines 803--810): for
unit-interval `x` and `0 ≤ z ≤ y`, `x^y ≤ x^z`. -/

private theorem sum_rpow_half_le_sum_rpow_one_thirtysecond
    (params : Parameters) (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1) :
    Real.rpow eps (1 / (2 : Error)) + Real.rpow delta (1 / (2 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2 : Error)) ≤
      Real.rpow eps (1 / (32 : Error)) + Real.rpow delta (1 / (32 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error)) := by
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  have hexp_nonneg : (0 : Error) ≤ 1 / (32 : Error) := by norm_num
  have hexp_le : (1 / (32 : Error)) ≤ 1 / (2 : Error) := by norm_num
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact Real.rpow_le_rpow_of_exponent_ge' heps heps_le_one hexp_nonneg hexp_le
  · exact Real.rpow_le_rpow_of_exponent_ge' hdelta hdelta_le_one hexp_nonneg hexp_le
  · exact Real.rpow_le_rpow_of_exponent_ge' hdq_nonneg hdq_le_one hexp_nonneg hexp_le

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
  have hmono :=
    sum_rpow_half_le_sum_rpow_one_thirtysecond params eps delta heps heps_le_one
      hdelta hdelta_le_one hdq_le_one
  have h3000m_nn : (0 : Error) ≤ 3000 * (params.m : Error) := by positivity
  -- Both sides expand to `3000 m * sum_p` for matching exponents `p`.
  unfold selfImprovementHelperError selfImprovementError
    MainInductionStep.selfImprovementInInductionError
  calc
    30 *
        (100 * (params.m : Error) *
          (Real.rpow eps (1 / (2 : Error)) +
            Real.rpow delta (1 / (2 : Error)) +
            Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2 : Error))))
        =
      3000 * (params.m : Error) *
        (Real.rpow eps (1 / (2 : Error)) +
          Real.rpow delta (1 / (2 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2 : Error))) := by
            ring
    _ ≤
      3000 * (params.m : Error) *
        (Real.rpow eps (1 / (32 : Error)) +
          Real.rpow delta (1 / (32 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32 : Error))) :=
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
  have hhelper_nn : 0 ≤ selfImprovementHelperError params eps delta := by
    have hmnn : (0 : Error) ≤ (params.m : Error) := m_cast_nonneg params
    have hdq_nn : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
      d_q_ratio_nonneg params
    have hsum_nn :
        (0 : Error) ≤ Real.rpow eps (1 / (2 : Error)) +
            Real.rpow delta (1 / (2 : Error)) +
            Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2 : Error)) := by
      have h1 := Real.rpow_nonneg heps (1 / (2 : Error))
      have h2 := Real.rpow_nonneg hdelta (1 / (2 : Error))
      have h3 := Real.rpow_nonneg hdq_nn (1 / (2 : Error))
      simpa [Real.rpow_eq_pow] using add_nonneg (add_nonneg h1 h2) h3
    change (0 : Error) ≤ 100 * (params.m : Error) *
        (Real.rpow eps (1 / (2 : Error)) +
          Real.rpow delta (1 / (2 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2 : Error)))
    positivity
  linarith

end MIPStarRE.LDT.SelfImprovement
