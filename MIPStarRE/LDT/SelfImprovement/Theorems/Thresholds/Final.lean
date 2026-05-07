import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds.Helper

/-!
# Section 9 — final-stage numerical threshold absorptions

This module contains the final-stage arithmetic comparisons which absorb the natural
projective-output error terms into the literal `selfImprovementError` threshold.
The estimates formalize the exponent-monotonicity bookkeeping in
`references/ldt-paper/self_improvement.tex`, lines 803--810, and are used by the
final-field producer statements in the self-improvement theorem.

The helper-stage estimates, including the square-root bound on the global-variance
error, are in `Thresholds.Helper`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective

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

/-- The final-stage power sum is nonnegative when its base parameters are
nonnegative.

This is the positivity fact used when multiplying coefficient comparisons by
`ε^p + δ^p + (d/q)^p`. -/
theorem finalStagePowerSum_nonneg
    (params : Parameters) (eps delta p : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    0 ≤ finalStagePowerSum params eps delta p := by
  unfold finalStagePowerSum
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    d_q_ratio_nonneg params
  exact add_nonneg
    (add_nonneg (Real.rpow_nonneg heps _) (Real.rpow_nonneg hdelta _))
    (Real.rpow_nonneg hdq_nonneg _)

/-- Exponent monotonicity for the final-stage power sum on the unit interval.

If `ε`, `δ`, and `d/q` all lie in `[0, 1]`, then increasing the exponent
decreases each term of the power sum. This is the formal arithmetic step behind
the final threshold comparison in `self_improvement.tex`, lines 803--810. -/
theorem finalStagePowerSum_le_of_exponent_ge
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

/-- The square root of a final-stage power sum is bounded by the power sum with
half the exponent.

The proof is the elementary estimate
`sqrt (x + y + z) ≤ sqrt x + sqrt y + sqrt z`, applied to the three powers
`ε^p`, `δ^p`, and `(d/q)^p`. -/
theorem sqrt_finalStagePowerSum_le
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

/-- The helper-stage threshold as the final-stage power sum with exponent
`1/2`.

This is definitionally equal to `selfImprovementHelperError`; the named lemma is
used to avoid unfolding the error definition inside later absorptions. -/
theorem selfImprovementHelperError_eq_finalStagePowerSum
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementHelperError params eps delta =
      100 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (2 : Error)) := by
  rfl

/-- The final self-improvement threshold as the final-stage power sum with
exponent `1/32`.

This records the literal error parameter appearing in the formal statement of
the self-improvement theorem. -/
theorem selfImprovementError_eq_finalStagePowerSum
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

/-- The orthogonalization threshold written as an iterated square root of the
helper threshold.

The paper writes the corresponding quantity as
`100 * \widehat{\zeta}^{1/4}`. This lemma gives the equivalent square-root
form used by the estimates which follow orthonormalization. -/
theorem selfImprovementOrthogonalizationError_eq
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementOrthogonalizationError params eps delta =
      100 * Real.sqrt (Real.sqrt (selfImprovementHelperError params eps delta)) := by
  unfold selfImprovementOrthogonalizationError orthonormalizationError
  rw [rpow_quarter_eq_sqrt_sqrt (selfImprovementHelperError_nonneg params eps delta)]

private theorem selfImprovementOrthogonalizationError_le_four_hundred_m_powerSum_eighth
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    selfImprovementOrthogonalizationError params eps delta ≤
      400 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (8 : Error)) := by
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
  rw [selfImprovementOrthogonalizationError_eq]
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

/-- The data-processing threshold written with an ordinary square root.

This is the displayed expression used after projecting the helper output:
`8\widehat{\zeta} + 8\sqrt{\widehat{\zeta}_{\mathrm{ortho}}}`. -/
theorem selfImprovementDataProcessingError_eq
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    selfImprovementDataProcessingError params eps delta =
      8 * selfImprovementHelperError params eps delta +
        8 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
  unfold selfImprovementDataProcessingError
  simp [Real.sqrt_eq_rpow, Real.rpow_eq_pow]

/-- The data-processing threshold contains the term `8 * selfImprovementHelperError`.

This lower bound is the scalar source of the alphabet-size obstruction in the
current point-consistency transport: once the total-overlap estimate contributes
`sqrt (#F_q * selfImprovementDataProcessingError)`, this positive summand carries
the cardinality of the alphabet into the final-stage error. -/
theorem eight_selfImprovementHelperError_le_selfImprovementDataProcessingError
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    8 * selfImprovementHelperError params eps delta ≤
      selfImprovementDataProcessingError params eps delta := by
  rw [selfImprovementDataProcessingError_eq]
  have horth_sqrt_nonneg :
      0 ≤ 8 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) := by
    positivity
  linarith

/-- The alphabet-size square-root term is bounded below by the corresponding
term coming from `8 * selfImprovementHelperError`.

This records that, in the present final-fields transport, the cardinality
factor cannot be removed by lower-bounding
`selfImprovementDataProcessingError` through `8 * selfImprovementHelperError`.
The structural obstruction is the surrounding estimate carrying
`sqrt (#F_q * selfImprovementDataProcessingError)` into a final threshold
which has no corresponding alphabet-size term. -/
theorem sqrt_card_mul_eight_helperError_le_sqrt_card_mul_dataProcessingError
    (params : Parameters) [FieldModel params.q] (eps delta : Error) :
    Real.sqrt
        ((Fintype.card (Fq params) : Error) *
          (8 * selfImprovementHelperError params eps delta)) ≤
      Real.sqrt
        ((Fintype.card (Fq params) : Error) *
          selfImprovementDataProcessingError params eps delta) := by
  exact Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left
      (eight_selfImprovementHelperError_le_selfImprovementDataProcessingError
        params eps delta)
      (by positivity))

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
  rw [selfImprovementDataProcessingError_eq]
  calc
    8 * selfImprovementHelperError params eps delta +
        8 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta)
        ≤ 8 * (100 * (params.m : Error) *
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

private theorem final_fields_projective_residual_error_le_131_times_finalStagePowerSum
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
      131 * (params.m : Error) *
        finalStagePowerSum params eps delta (1 / (32 : Error)) := by
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    d_q_ratio_le_one_of_d_le_q params hd_le_q
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
  have hdata_sqrt :
      Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
        31 * (params.m : Error) * finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    exact sqrt_selfImprovementDataProcessingError_le_thirty_one_m_powerSum_thirtysecond
      params eps delta heps heps_le_one hdelta hdelta_le_one hdq_le_one
  nlinarith

/-- Final projective-residual threshold absorption (`self_improvement.tex`,
lines 803--810).

The natural error emitted by the projective residual producer is
`ζ̂ + √ζ̂_dataprocess`. Under the standard unit-interval hypotheses for
`ε`, `δ`, and `d/q`, this theorem absorbs that natural error into the literal
`selfImprovementError` threshold used by `SelfImprovementConclusion`.  Lean
records the third unit-interval hypothesis as `d ≤ q`, equivalently `d/q ≤ 1`
because `q` is positive. -/
theorem final_fields_projective_residual_error_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
      selfImprovementError params eps delta := by
  have hhelper := final_fields_projective_residual_error_le_131_times_finalStagePowerSum params
    eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
  have hsum32_nn :
      0 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_nonneg params eps delta (1 / (32 : Error)) heps hdelta
  have hcoef :
      131 * (params.m : Error) ≤ 3000 * (params.m : Error) := by
    nlinarith [m_cast_nonneg params]
  calc
    selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
        131 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := hhelper
    _ ≤ 3000 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) :=
        mul_le_mul_of_nonneg_right hcoef hsum32_nn
    _ = selfImprovementError params eps delta := by
      rw [selfImprovementError_eq_finalStagePowerSum]


/-- Small-alphabet branch for projective residual transport.

When `|F_q| ≤ 8464`, we additionally have `√|F_q| ≤ 92`, and the extra data-processing
overlap contribution is absorbed into the final threshold by the same coefficient bookkeeping
as in `final_fields_projective_residual_error_le_selfImprovementError`.

The explicit bound `|F_q| ≤ 8464` is a concrete branch condition; it is not implied by
the standing unit-interval hypotheses and is isolated here so the dependency is explicit.
-/
theorem final_fields_projective_residual_error_le_selfImprovementError_of_small_alphabet
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (hq_le : Fintype.card (Fq params) ≤ 8464) :
    selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) +
        Real.sqrt ((Fintype.card (Fq params) : Error) *
          selfImprovementDataProcessingError params eps delta) ≤
      selfImprovementError params eps delta := by
  have hhelper_sqrt :=
    final_fields_projective_residual_error_le_131_times_finalStagePowerSum params
      eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    d_q_ratio_le_one_of_d_le_q params hd_le_q
  have hsum32_nonneg :
      0 ≤ finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    finalStagePowerSum_nonneg params eps delta (1 / (32 : Error)) heps hdelta
  have hdata_sqrt :
      Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
        31 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) :=
    sqrt_selfImprovementDataProcessingError_le_thirty_one_m_powerSum_thirtysecond
      params eps delta heps heps_le_one hdelta hdelta_le_one hdq_le_one
  have hdata_nonneg : 0 ≤ selfImprovementDataProcessingError params eps delta := by
    rw [selfImprovementDataProcessingError_eq]
    positivity
  have hcard_le :
      (Fintype.card (Fq params) : Error) * selfImprovementDataProcessingError params eps delta ≤
        (8464 : Error) * selfImprovementDataProcessingError params eps delta := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hq_le) hdata_nonneg
  have hsqrt_card_mul :
      Real.sqrt ((Fintype.card (Fq params) : Error) *
          selfImprovementDataProcessingError params eps delta) ≤
        Real.sqrt ((8464 : Error) *
          selfImprovementDataProcessingError params eps delta) :=
    Real.sqrt_le_sqrt hcard_le
  have hsqrt_data :
      Real.sqrt ((8464 : Error) * selfImprovementDataProcessingError params eps delta) =
      92 * Real.sqrt (selfImprovementDataProcessingError params eps delta) := by
    have h8464_nonneg : (0 : Error) ≤ (8464 : Error) := by norm_num
    calc
      Real.sqrt ((8464 : Error) * selfImprovementDataProcessingError params eps delta) =
          Real.sqrt (8464 : Error) *
            Real.sqrt (selfImprovementDataProcessingError params eps delta) := by
              rw [Real.sqrt_mul h8464_nonneg]
      _ = 92 * Real.sqrt (selfImprovementDataProcessingError params eps delta) := by
        norm_num
  have hsqrt_card : Real.sqrt ((Fintype.card (Fq params) : Error) *
      selfImprovementDataProcessingError params eps delta) ≤
    92 * Real.sqrt (selfImprovementDataProcessingError params eps delta) := by
    exact hsqrt_card_mul.trans hsqrt_data
  have hcard_term :
      Real.sqrt ((Fintype.card (Fq params) : Error) *
          selfImprovementDataProcessingError params eps delta) ≤
        2852 * (params.m : Error) *
          finalStagePowerSum params eps delta (1 / (32 : Error)) := by
    calc
      Real.sqrt ((Fintype.card (Fq params) : Error) *
          selfImprovementDataProcessingError params eps delta) ≤
          92 * Real.sqrt (selfImprovementDataProcessingError params eps delta) := hsqrt_card
      _ ≤ 92 * (31 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (32 : Error))) :=
          mul_le_mul_of_nonneg_left hdata_sqrt (by norm_num)
      _ = 2852 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (32 : Error)) := by ring_nf
  calc
    selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) +
        Real.sqrt ((Fintype.card (Fq params) : Error) *
          selfImprovementDataProcessingError params eps delta)
      ≤ 131 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (32 : Error)) +
          2852 * (params.m : Error) *
            finalStagePowerSum params eps delta (1 / (32 : Error)) := by
              nlinarith [hhelper_sqrt, hcard_term]
  _ = 2983 * (params.m : Error) *
      finalStagePowerSum params eps delta (1 / (32 : Error)) := by ring_nf
  _ ≤ 3000 * (params.m : Error) *
      finalStagePowerSum params eps delta (1 / (32 : Error)) := by
        have hm_nonneg : 0 ≤ (params.m : Error) := m_cast_nonneg params
        nlinarith [hm_nonneg, hsum32_nonneg]
  _ = selfImprovementError params eps delta := by
    rw [selfImprovementError_eq_finalStagePowerSum]

/-- Final completeness threshold absorption (`self_improvement.tex`,
lines 803--810).

The natural error emitted by the projective completeness transport is
`2ζ̂ + 2 sqrt ζ̂_ortho`. Under the standard unit-interval hypotheses for
`ε`, `δ`, and `d/q`, this theorem absorbs that natural error into the literal
`selfImprovementError` threshold used by `SelfImprovementFinalFields`.  Lean
records the third unit-interval hypothesis as `d ≤ q`, equivalently `d/q ≤ 1`
because `q` is positive. -/
theorem final_fields_completeness_error_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    2 * selfImprovementHelperError params eps delta +
        2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta) ≤
      selfImprovementError params eps delta := by
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    d_q_ratio_le_one_of_d_le_q params hd_le_q
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
Lean records the third unit-interval hypothesis as `d ≤ q`, equivalently
`d/q ≤ 1` because `q` is positive.
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
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    d_q_ratio_le_one_of_d_le_q params hd_le_q
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
absorptions are derived.  The hypothesis `hd_le_q` records the paper's
small-error branch `d/q ≤ 1`, using positivity of `q`. -/
theorem thirty_selfImprovementHelperError_le_selfImprovementError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error)) :
    30 * selfImprovementHelperError params eps delta ≤
      selfImprovementError params eps delta := by
  have hdq_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 :=
    d_q_ratio_le_one_of_d_le_q params hd_le_q
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
    selfImprovementHelperError_nonneg params eps delta
  linarith


end MIPStarRE.LDT.SelfImprovement
