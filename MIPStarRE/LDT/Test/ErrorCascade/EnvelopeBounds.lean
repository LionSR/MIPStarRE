import MIPStarRE.LDT.Test.ErrorCascade.Definitions

/-!
# Error cascade — envelope and root bounding machinery

Internal helper lemmas for the error-cascade bookkeeping of Step 8.
These provide the step-envelope interpolation (`stepEnvelope`),
monotonicity under denominator enlargement, square-root scaling, and
explicit numeric bounds on various `rpow` and `sqrt` expressions.
All lemmas are technical and should not be part of downstream API.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

/-- A paper-local envelope with exponent `1/n` and decay scale `N`. -/
noncomputable def stepEnvelope (params : Parameters) (k : ℕ) (eps : Error)
    (n N : Error) : Error :=
  Real.rpow eps (1 / n) +
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / n) +
    Real.exp (-((k : Error) / (N * ((params.m : Error) ^ (2 : ℕ)))))

theorem mainFormalEnvelope_eq_stepEnvelope (params : Parameters) (k : ℕ) (eps : Error) :
    mainFormalEnvelope params k eps =
      stepEnvelope params k eps (40000 : Error) (2560000 : Error) := rfl

/-- For `x ∈ [0, 1]`, enlarging the denominator in `x^(1/n)` makes the
exponent smaller and therefore the value larger. -/
theorem rpow_le_of_denom_le {x : Error} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n₁ n₂ : Error} (hn₁Pos : 0 < n₁) (hn : n₁ ≤ n₂) :
    Real.rpow x (1 / n₁) ≤ Real.rpow x (1 / n₂) := by
  have hn₂Pos : 0 < n₂ := lt_of_lt_of_le hn₁Pos hn
  have hdiv : 1 / n₂ ≤ 1 / n₁ := one_div_le_one_div_of_le hn₁Pos hn
  exact Real.rpow_le_rpow_of_exponent_ge' hx hx1 (show 0 ≤ 1 / n₂ by positivity) hdiv

/-- For `k ≥ 0`, `m > 0`, and `N₁ ≤ N₂`, the larger decay denominator gives
the weaker exponential bound `exp(-k/(N₁ m²)) ≤ exp(-k/(N₂ m²))`. -/
theorem exp_neg_le_of_denom_ge (k : ℕ) (m : Error) (hm : 0 < m)
    {N₁ N₂ : Error} (h₁ : 0 < N₁) (h₁₂ : N₁ ≤ N₂) :
    Real.exp (-((k : Error) / (N₁ * m ^ (2 : ℕ)))) ≤
      Real.exp (-((k : Error) / (N₂ * m ^ (2 : ℕ)))) := by
  have hm2 : 0 < m ^ (2 : ℕ) := by positivity
  have hN₁m : 0 < N₁ * m ^ 2 := mul_pos h₁ hm2
  have hknn : (0 : Error) ≤ (k : Error) := Nat.cast_nonneg _
  have hratio : (k : Error) / (N₂ * m ^ 2) ≤ (k : Error) / (N₁ * m ^ 2) := by
    apply div_le_div_of_nonneg_left hknn hN₁m
    exact mul_le_mul_of_nonneg_right h₁₂ hm2.le
  exact Real.exp_le_exp.mpr (neg_le_neg hratio)

theorem stepEnvelope_nonneg {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error} :
    0 ≤ stepEnvelope params k eps n N := by
  unfold stepEnvelope
  refine add_nonneg (add_nonneg (Real.rpow_nonneg h.hepsNN _) ?_) (Real.exp_nonneg _)
  exact Real.rpow_nonneg h.dqNN _

theorem stepEnvelope_le_stepEnvelope {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n₁ n₂ N₁ N₂ : Error}
    (hn₁Pos : 0 < n₁) (hn : n₁ ≤ n₂) (hN₁Pos : 0 < N₁) (hN : N₁ ≤ N₂) :
    stepEnvelope params k eps n₁ N₁ ≤ stepEnvelope params k eps n₂ N₂ := by
  unfold stepEnvelope
  have hEps := rpow_le_of_denom_le h.hepsNN h.hepsOne hn₁Pos hn
  have hDq := rpow_le_of_denom_le h.dqNN h.dqLeOne hn₁Pos hn
  have hmPos : 0 < (params.m : Error) := by linarith [h.hm]
  have hExp := exp_neg_le_of_denom_ge k (params.m : Error) hmPos hN₁Pos hN
  linarith

/-- A paper-local envelope with exponent `1/n` and decay scale `N` is absorbed
by `mainFormalEnvelope` whenever `n ≤ 40000` and `N ≤ 2560000`. -/
theorem stepEnvelope_le_mainFormalEnvelope {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error}
    (hnPos : 0 < n) (hn : n ≤ 40000) (hNPos : 0 < N) (hN : N ≤ 2560000) :
    stepEnvelope params k eps n N ≤ mainFormalEnvelope params k eps := by
  calc
    stepEnvelope params k eps n N ≤ stepEnvelope params k eps (40000 : Error) (2560000 : Error) :=
      stepEnvelope_le_stepEnvelope (h := h) (hn₁Pos := hnPos) (hn := hn)
        (hN₁Pos := hNPos) (hN := hN)
    _ = mainFormalEnvelope params k eps := by rw [mainFormalEnvelope_eq_stepEnvelope]

theorem sqrt_rpow_one_div {x n : Error} (hx : 0 ≤ x) (_hn : 0 < n) :
    Real.sqrt (Real.rpow x (1 / n)) = Real.rpow x (1 / (2 * n)) := by
  have hn0 : n ≠ 0 := by linarith
  rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (Real.rpow x (1 / n)) (1 / (2 : Error))
      = Real.rpow x ((1 / n) * (1 / (2 : Error))) := by
          simpa using (Real.rpow_mul hx (1 / n) (1 / (2 : Error))).symm
    _ = Real.rpow x (1 / (2 * n)) := by
      field_simp [hn0]

theorem sqrt_exp_neg_div (k : ℕ) (m N : Error) (hm : 0 < m) (hN : 0 < N) :
    Real.sqrt (Real.exp (-((k : Error) / (N * m ^ (2 : ℕ))))) =
      Real.exp (-((k : Error) / ((2 * N) * m ^ (2 : ℕ)))) := by
  rw [← Real.exp_half]
  congr 1
  field_simp [hm.ne', hN.ne']

theorem sqrt_stepEnvelope_le {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error} (hn : 0 < n) (hN : 0 < N) :
    Real.sqrt (stepEnvelope params k eps n N) ≤ stepEnvelope params k eps (2 * n) (2 * N) := by
  have hmPos : 0 < (params.m : Error) := by linarith [h.hm]
  unfold stepEnvelope
  calc
    Real.sqrt
        (Real.rpow eps (1 / n) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / n) +
          Real.exp (-((k : Error) / (N * ((params.m : Error) ^ (2 : ℕ))))))
      ≤ Real.sqrt (Real.rpow eps (1 / n)) +
          Real.sqrt (Real.rpow ((params.d : Error) / (params.q : Error)) (1 / n)) +
          Real.sqrt (Real.exp (-((k : Error) / (N * ((params.m : Error) ^ (2 : ℕ)))))) :=
        sqrt_add3_le_add3_sqrt (Real.rpow_nonneg h.hepsNN _) (Real.rpow_nonneg h.dqNN _)
          (Real.exp_nonneg _)
    _ = stepEnvelope params k eps (2 * n) (2 * N) := by
      rw [sqrt_rpow_one_div h.hepsNN hn, sqrt_rpow_one_div h.dqNN hn,
        sqrt_exp_neg_div k (params.m : Error) N hmPos hN]
      rfl

theorem stepEnvelope_le_sq_stepEnvelope {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error} (hn : 0 < n) (hN : 0 < N) :
    stepEnvelope params k eps n N ≤
      (stepEnvelope params k eps (2 * n) (2 * N)) ^ (2 : ℕ) := by
  let F : Error := stepEnvelope params k eps (2 * n) (2 * N)
  have hsqrt := sqrt_stepEnvelope_le (h := h) (n := n) (N := N) hn hN
  have hnn : 0 ≤ stepEnvelope params k eps n N := stepEnvelope_nonneg (h := h) (n := n) (N := N)
  have hFnn : 0 ≤ F := by
    simpa [F] using stepEnvelope_nonneg (h := h) (n := 2 * n) (N := 2 * N)
  have hsq : (Real.sqrt (stepEnvelope params k eps n N)) ^ (2 : ℕ) ≤ F ^ (2 : ℕ) := by
    exact (sq_le_sq).2 (by
      simpa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hFnn, F] using hsqrt)
  simpa [F, Real.sq_sqrt hnn] using hsq

theorem self_le_rpow_one_div {x : Error} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n : Error} (hn : 1 ≤ n) :
    x ≤ Real.rpow x (1 / n) := by
  have hnPos : 0 < n := by linarith
  have hdiv : 1 / n ≤ (1 : Error) := by
    field_simp [hnPos.ne']
    linarith
  simpa [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_ge' hx hx1 (show 0 ≤ 1 / n by positivity) hdiv)

theorem m_le_k2m4_aux {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    (params.m : Error) ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
  calc
    (params.m : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := h.m_le_m4
    _ = 1 * ((params.m : Error) ^ (4 : ℕ)) := by ring
    _ ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right h.k2_ge_one (by positivity)

theorem dq_le_rpow2048 {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    (params.d : Error) / (params.q : Error) ≤
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) :=
  self_le_rpow_one_div h.dqNN h.dqLeOne (by norm_num)

theorem dq_rpow2048_le_stepEnvelope2048 {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) ≤
      stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  unfold stepEnvelope
  have hepsNN' : 0 ≤ Real.rpow eps (1 / (2048 : Error)) := Real.rpow_nonneg h.hepsNN _
  have hExpNN' :
      0 ≤ Real.exp (-((k : Error) / ((160000 : Error) * ((params.m : Error) ^ (2 : ℕ))))) :=
    Real.exp_nonneg _
  exact (le_add_of_nonneg_left hepsNN').trans (le_add_of_nonneg_right hExpNN')

theorem mdq_le_k2m4_stepEnvelope2048 {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    (params.m : Error) * ((params.d : Error) / (params.q : Error)) ≤
      ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  have hTNN : 0 ≤ stepEnvelope params k eps (2048 : Error) (160000 : Error) :=
    stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hdq_to_T :
      (params.d : Error) / (params.q : Error) ≤
        stepEnvelope params k eps (2048 : Error) (160000 : Error) :=
    (dq_le_rpow2048 h).trans (dq_rpow2048_le_stepEnvelope2048 h)
  have hmdq_to_mT : (params.m : Error) * ((params.d : Error) / (params.q : Error)) ≤
      (params.m : Error) * stepEnvelope params k eps (2048 : Error) (160000 : Error) :=
    mul_le_mul_of_nonneg_left hdq_to_T (Nat.cast_nonneg params.m)
  have hmT : (params.m : Error) * stepEnvelope params k eps (2048 : Error) (160000 : Error) ≤
      (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ))) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) :=
    mul_le_mul_of_nonneg_right (m_le_k2m4_aux (h := h)) hTNN
  exact hmdq_to_mT.trans hmT

theorem four_mul_le_k2m4_mul {params : Parameters} {k : ℕ} {eps T : Error}
    (h : CascadeHypotheses params k eps) (hT : 0 ≤ T) :
    4 * T ≤ 4 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ))) * T := by
  have hscale : (4 : Error) ≤ 4 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ))) := by
    simpa using mul_le_mul_of_nonneg_left h.k2_m4_ge_one (by norm_num : (0 : Error) ≤ 4)
  exact mul_le_mul_of_nonneg_right hscale hT

theorem sqrt_three_le_two : Real.sqrt (3 : Error) ≤ 2 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

theorem sqrt20000_le_142 : Real.sqrt (20000 : Error) ≤ 142 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

theorem sqrt20204_le_143 : Real.sqrt (20204 : Error) ≤ 143 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

theorem sqrt150000_le_388 : Real.sqrt (150000 : Error) ≤ 388 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

theorem sqrt170244_le_413 : Real.sqrt (170244 : Error) ≤ 413 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

theorem two_sqrt40005_le_401 : 2 * Real.sqrt (40005 : Error) ≤ 401 := by
  have hsqrt : Real.sqrt (40005 : Error) ≤ 401 / 2 := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor <;> norm_num
  nlinarith

theorem rpow20204_quarter_le_12 : Real.rpow (20204 : Error) (1 / (4 : Error)) ≤ 12 := by
  have hmono := Real.rpow_le_rpow (show 0 ≤ (20204 : Error) by norm_num)
    (by norm_num : (20204 : Error) ≤ (12 : Error) ^ (4 : ℕ)) (by positivity : 0 ≤ (1 / (4 : Error)))
  calc
    Real.rpow (20204 : Error) (1 / (4 : Error))
      ≤ Real.rpow ((12 : Error) ^ (4 : ℕ)) (1 / (4 : Error)) := hmono
    _ = Real.rpow (12 : Error) ((4 : Error) * (1 / (4 : Error))) := by
      symm
      exact Real.rpow_natCast_mul (by norm_num : 0 ≤ (12 : Error)) 4 (1 / (4 : Error))
    _ = (12 : Error) := by norm_num [Real.rpow_one]

theorem rpow20204_eighth_le_4 : Real.rpow (20204 : Error) (1 / (8 : Error)) ≤ 4 := by
  have hmono := Real.rpow_le_rpow (show 0 ≤ (20204 : Error) by norm_num)
    (by norm_num : (20204 : Error) ≤ (4 : Error) ^ (8 : ℕ)) (by positivity : 0 ≤ (1 / (8 : Error)))
  calc
    Real.rpow (20204 : Error) (1 / (8 : Error))
      ≤ Real.rpow ((4 : Error) ^ (8 : ℕ)) (1 / (8 : Error)) := hmono
    _ = Real.rpow (4 : Error) ((8 : Error) * (1 / (8 : Error))) := by
      symm
      exact Real.rpow_natCast_mul (by norm_num : 0 ≤ (4 : Error)) 8 (1 / (8 : Error))
    _ = (4 : Error) := by norm_num [Real.rpow_one]

theorem k2_rpow_quarter_le {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow ((k : Error) ^ (2 : ℕ)) (1 / (4 : Error)) ≤ (k : Error) := by
  calc
    Real.rpow ((k : Error) ^ (2 : ℕ)) (1 / (4 : Error))
      = Real.rpow (k : Error) ((2 : Error) * (1 / (4 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (k : Error)) 2 (1 / (4 : Error))
    _ = Real.rpow (k : Error) (1 / (2 : Error)) := by norm_num
    _ ≤ (k : Error) := by
      simpa using Real.rpow_le_self_of_one_le h.hk (by norm_num : (1 / (2 : Error)) ≤ 1)

theorem m4_rpow_quarter_eq {params : Parameters} :
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (4 : Error)) = (params.m : Error) := by
  calc
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (4 : Error))
      = Real.rpow (params.m : Error) ((4 : Error) * (1 / (4 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (params.m : Error)) 4 (1 / (4 : Error))
    _ = (params.m : Error) := by norm_num [Real.rpow_one]

theorem k2_rpow_eighth_le {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow ((k : Error) ^ (2 : ℕ)) (1 / (8 : Error)) ≤ (k : Error) := by
  calc
    Real.rpow ((k : Error) ^ (2 : ℕ)) (1 / (8 : Error))
      = Real.rpow (k : Error) ((2 : Error) * (1 / (8 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (k : Error)) 2 (1 / (8 : Error))
    _ = Real.rpow (k : Error) (1 / (4 : Error)) := by norm_num
    _ ≤ (k : Error) := by
      simpa using Real.rpow_le_self_of_one_le h.hk (by norm_num : (1 / (4 : Error)) ≤ 1)

theorem m4_rpow_eighth_le {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (8 : Error)) ≤ (params.m : Error) := by
  calc
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (8 : Error))
      = Real.rpow (params.m : Error) ((4 : Error) * (1 / (8 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (params.m : Error)) 4 (1 / (8 : Error))
    _ = Real.rpow (params.m : Error) (1 / (2 : Error)) := by norm_num
    _ ≤ (params.m : Error) := by
      simpa using Real.rpow_le_self_of_one_le h.hm (by norm_num : (1 / (2 : Error)) ≤ 1)

theorem rpow_one_four_eq_sqrt_sqrt {x : Error} (hx : 0 ≤ x) :
    Real.rpow x (1 / (4 : Error)) = Real.sqrt (Real.sqrt x) := by
  calc
    Real.rpow x (1 / (4 : Error)) =
        Real.rpow x ((1 / (2 : Error)) * (1 / (2 : Error))) := by
      norm_num
    _ = Real.rpow (Real.rpow x (1 / (2 : Error))) (1 / (2 : Error)) := by
      simpa using (Real.rpow_mul hx (1 / (2 : Error)) (1 / (2 : Error)))
    _ = Real.sqrt (Real.sqrt x) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rfl

theorem rpow_one_eight_eq_sqrt_sqrt_sqrt {x : Error} (hx : 0 ≤ x) :
    Real.rpow x (1 / (8 : Error)) = Real.sqrt (Real.sqrt (Real.sqrt x)) := by
  calc
    Real.rpow x (1 / (8 : Error)) =
        Real.rpow x ((1 / (4 : Error)) * (1 / (2 : Error))) := by
      norm_num
    _ = Real.rpow (Real.rpow x (1 / (4 : Error))) (1 / (2 : Error)) := by
      simpa using (Real.rpow_mul hx (1 / (4 : Error)) (1 / (2 : Error)))
    _ = Real.sqrt (Real.sqrt (Real.sqrt x)) := by
      rw [Real.sqrt_eq_rpow, rpow_one_four_eq_sqrt_sqrt hx]
      rfl

theorem stepEnvelope_rpow_quarter_le {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow (stepEnvelope params k eps (2048 : Error) (160000 : Error)) (1 / (4 : Error)) ≤
      stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
  have h1 : Real.sqrt (stepEnvelope params k eps (2048 : Error) (160000 : Error)) ≤
      stepEnvelope params k eps (4096 : Error) (320000 : Error) := by
    simpa [show (2 : Error) * 2048 = 4096 by norm_num,
      show (2 : Error) * 160000 = 320000 by norm_num] using
      sqrt_stepEnvelope_le (h := h) (n := (2048 : Error)) (N := (160000 : Error))
        (by norm_num) (by norm_num)
  have h2 : Real.sqrt (stepEnvelope params k eps (4096 : Error) (320000 : Error)) ≤
      stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
    simpa [show (2 : Error) * 4096 = 8192 by norm_num,
      show (2 : Error) * 320000 = 640000 by norm_num] using
      sqrt_stepEnvelope_le (h := h) (n := (4096 : Error)) (N := (320000 : Error))
        (by norm_num) (by norm_num)
  have hnn : 0 ≤ stepEnvelope params k eps (2048 : Error) (160000 : Error) :=
    stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  calc
    Real.rpow (stepEnvelope params k eps (2048 : Error) (160000 : Error)) (1 / (4 : Error))
      = Real.sqrt (Real.sqrt (stepEnvelope params k eps (2048 : Error) (160000 : Error))) :=
        rpow_one_four_eq_sqrt_sqrt hnn
    _ ≤ Real.sqrt (stepEnvelope params k eps (4096 : Error) (320000 : Error)) :=
      Real.sqrt_le_sqrt h1
    _ ≤ stepEnvelope params k eps (8192 : Error) (640000 : Error) := h2

theorem stepEnvelope_rpow_eighth_le {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow (stepEnvelope params k eps (2048 : Error) (160000 : Error)) (1 / (8 : Error)) ≤
      stepEnvelope params k eps (16384 : Error) (1280000 : Error) := by
  have h1 : Real.sqrt (stepEnvelope params k eps (2048 : Error) (160000 : Error)) ≤
      stepEnvelope params k eps (4096 : Error) (320000 : Error) := by
    simpa [show (2 : Error) * 2048 = 4096 by norm_num,
      show (2 : Error) * 160000 = 320000 by norm_num] using
      sqrt_stepEnvelope_le (h := h) (n := (2048 : Error)) (N := (160000 : Error))
        (by norm_num) (by norm_num)
  have h2 : Real.sqrt (stepEnvelope params k eps (4096 : Error) (320000 : Error)) ≤
      stepEnvelope params k eps (8192 : Error) (640000 : Error) := by
    simpa [show (2 : Error) * 4096 = 8192 by norm_num,
      show (2 : Error) * 320000 = 640000 by norm_num] using
      sqrt_stepEnvelope_le (h := h) (n := (4096 : Error)) (N := (320000 : Error))
        (by norm_num) (by norm_num)
  have h3 : Real.sqrt (stepEnvelope params k eps (8192 : Error) (640000 : Error)) ≤
      stepEnvelope params k eps (16384 : Error) (1280000 : Error) := by
    simpa [show (2 : Error) * 8192 = 16384 by norm_num,
      show (2 : Error) * 640000 = 1280000 by norm_num] using
      sqrt_stepEnvelope_le (h := h) (n := (8192 : Error)) (N := (640000 : Error))
        (by norm_num) (by norm_num)
  have hnn : 0 ≤ stepEnvelope params k eps (2048 : Error) (160000 : Error) :=
    stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  calc
    Real.rpow (stepEnvelope params k eps (2048 : Error) (160000 : Error))
        (1 / (8 : Error))
      = Real.sqrt
          (Real.sqrt (Real.sqrt (stepEnvelope params k eps (2048 : Error) (160000 : Error)))) :=
        rpow_one_eight_eq_sqrt_sqrt_sqrt hnn
    _ ≤ Real.sqrt (Real.sqrt (stepEnvelope params k eps (4096 : Error) (320000 : Error))) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h1)
    _ ≤ Real.sqrt (stepEnvelope params k eps (8192 : Error) (640000 : Error)) :=
      Real.sqrt_le_sqrt h2
    _ ≤ stepEnvelope params k eps (16384 : Error) (1280000 : Error) := h3

theorem sqrt_scaled_stepEnvelope_le {params : Parameters} {k : ℕ} {eps x C n N : Error}
    (h : CascadeHypotheses params k eps)
    (hC : 0 ≤ C)
    (hx : x ≤ C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
      stepEnvelope params k eps n N)
    (hn : 0 < n) (hN : 0 < N) :
    Real.sqrt x ≤
      Real.sqrt C * (k : Error) * ((params.m : Error) ^ (2 : ℕ)) *
        stepEnvelope params k eps (2 * n) (2 * N) := by
  set E : Error := stepEnvelope params k eps (2 * n) (2 * N)
  have hE_sq : stepEnvelope params k eps n N ≤ E ^ (2 : ℕ) := by
    simpa [E] using stepEnvelope_le_sq_stepEnvelope (h := h) (n := n) (N := N) hn hN
  have hCoeffNN : 0 ≤ C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  have hENN : 0 ≤ E := by
    simpa [E] using stepEnvelope_nonneg (h := h) (n := 2 * n) (N := 2 * N)
  have hx' : x ≤ C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) * E ^ (2 : ℕ) := by
    calc
      x ≤ C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
            stepEnvelope params k eps n N := hx
      _ ≤ C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) * E ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hE_sq hCoeffNN
  set u : Error := (k : Error) * ((params.m : Error) ^ (2 : ℕ)) * E
  have huNN : 0 ≤ u := by
    dsimp [u]
    positivity [hENN]
  have hsqrt := Real.sqrt_le_sqrt hx'
  calc
    Real.sqrt x ≤
        Real.sqrt (C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) * E ^ (2 : ℕ)) :=
      hsqrt
    _ = Real.sqrt (C * (u ^ (2 : ℕ))) := by
      rw [show C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) * E ^ (2 : ℕ) =
          C * (u ^ (2 : ℕ)) by
        dsimp [u]
        ring]
    _ = Real.sqrt C * u := by
      rw [Real.sqrt_mul hC, Real.sqrt_sq_eq_abs, abs_of_nonneg huNN]
    _ = Real.sqrt C * (k : Error) * ((params.m : Error) ^ (2 : ℕ)) *
          stepEnvelope params k eps (2 * n) (2 * N) := by
      simp [u, E]
      ring

theorem rpow_Z1_factor_le {params : Parameters} {k : ℕ}
    {Z1 k2 m4 E2048 r Crpow Erpow : Error}
    (hZ1NN : 0 ≤ Z1)
    (hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048)
    (hrNN : 0 ≤ r)
    (hk2NN : 0 ≤ k2)
    (hm4NN : 0 ≤ m4)
    (hE2048NN : 0 ≤ E2048)
    (hA : Real.rpow (20204 : Error) r ≤ Crpow)
    (hB : Real.rpow k2 r ≤ (k : Error))
    (hC : Real.rpow m4 r ≤ (params.m : Error))
    (hD : Real.rpow E2048 r ≤ Erpow) :
    Real.rpow Z1 r ≤ Crpow * (k : Error) * (params.m : Error) * Erpow := by
  set A : Error := Real.rpow (20204 : Error) r
  set B : Error := Real.rpow k2 r
  set C : Error := Real.rpow m4 r
  set D : Error := Real.rpow E2048 r
  have hAnn : 0 ≤ A := by
    simpa [A] using Real.rpow_nonneg (by norm_num : 0 ≤ (20204 : Error)) r
  have hBnn : 0 ≤ B := by
    simpa [B] using Real.rpow_nonneg hk2NN r
  have hCnn : 0 ≤ C := by
    simpa [C] using Real.rpow_nonneg hm4NN r
  have hDnn : 0 ≤ D := by
    simpa [D] using Real.rpow_nonneg hE2048NN r
  have hCrpowNN : 0 ≤ Crpow := le_trans hAnn hA
  have hkNN : 0 ≤ (k : Error) := Nat.cast_nonneg _
  have hmNN : 0 ≤ (params.m : Error) := Nat.cast_nonneg _
  have hAB : A * B ≤ Crpow * (k : Error) :=
    mul_le_mul hA hB hBnn hCrpowNN
  have hABC : A * B * C ≤ (Crpow * (k : Error)) * (params.m : Error) := by
    exact mul_le_mul hAB hC hCnn (mul_nonneg hCrpowNN hkNN)
  have hABCD : A * B * C * D ≤ ((Crpow * (k : Error)) * (params.m : Error)) * Erpow := by
    exact mul_le_mul hABC hD hDnn (mul_nonneg (mul_nonneg hCrpowNN hkNN) hmNN)
  have hsplit1 :
      Real.rpow (((20204 : Error) * k2) * (m4 * E2048)) r =
        Real.rpow ((20204 : Error) * k2) r * Real.rpow (m4 * E2048) r := by
    simpa using
      (Real.mul_rpow (x := ((20204 : Error) * k2)) (y := (m4 * E2048)) (z := r)
        (by positivity) (mul_nonneg hm4NN hE2048NN))
  have hsplit2a :
      Real.rpow ((20204 : Error) * k2) r =
        Real.rpow (20204 : Error) r * Real.rpow k2 r := by
    simpa using
      (Real.mul_rpow (x := (20204 : Error)) (y := k2) (z := r) (by positivity) hk2NN)
  have hsplit2b :
      Real.rpow (m4 * E2048) r = Real.rpow m4 r * Real.rpow E2048 r := by
    simpa using (Real.mul_rpow (x := m4) (y := E2048) (z := r) hm4NN hE2048NN)
  have hFactor : Real.rpow (20204 * k2 * m4 * E2048) r = A * B * C * D := by
    calc
      Real.rpow (20204 * k2 * m4 * E2048) r
          = Real.rpow (((20204 : Error) * k2) * (m4 * E2048)) r := by
              congr 1
              ring
      _ = Real.rpow ((20204 : Error) * k2) r * Real.rpow (m4 * E2048) r := hsplit1
      _ = (Real.rpow (20204 : Error) r * Real.rpow k2 r) *
            (Real.rpow m4 r * Real.rpow E2048 r) := by
            rw [hsplit2a, hsplit2b]
      _ = A * B * C * D := by simp [A, B, C, D, mul_assoc, mul_left_comm, mul_comm]
  calc
    Real.rpow Z1 r ≤ Real.rpow (20204 * k2 * m4 * E2048) r :=
      Real.rpow_le_rpow hZ1NN hZ1 hrNN
    _ = A * B * C * D := hFactor
    _ ≤ Crpow * (k : Error) * (params.m : Error) * Erpow := by
      simpa [mul_assoc] using hABCD

end Test

end MIPStarRE.LDT
