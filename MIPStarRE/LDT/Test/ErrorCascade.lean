import Mathlib.Analysis.Complex.ExponentialBounds
import MIPStarRE.LDT.Test.MainTheorem

/-!
# Section 3 — Error cascade bounds for `mainFormal` (Step 8/8)

This module discharges the final bookkeeping step of the proof of `mainFormal`
from `references/ldt-paper/inductive_step.tex:187-234`. It names the five
intermediate real-valued error quantities `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄` that
appear through the unsymmetrization → Schwartz–Zippel → orthonormalization →
completion chain, and shows that each is absorbed by the final
`mainFormalError` envelope.

The absorbing conclusions all target the common envelope
`ε^(1/40000) + (d/q)^(1/40000) + exp(-k/(2560000 m²))`, which coincides with
the unscaled factor of `mainFormalError`; see `mainFormalError_eq_envelope`.
The upstream hypotheses are stated at the paper's native exponents and decay
scales (`1/1024`, `1/2048`, `1/16384`, `1/32768`) and are coarsened to this
common envelope inside the Lean proofs.

Each cascade-step lemma has two components:

* The **cascade variable** (`cascadeSigma`, `cascadeZeta1`, …), a
  paper-faithful definition of the intermediate quantity.
* The **tight cascade bound** (`cascadeZeta1_bound`, …), deriving the paper's
  native estimate directly from the cascade definition.
* The **absorbing bound** (`sigma_bound`, `zeta1_bound`, …), coarsening the
  tight estimate to the final `mainFormalError` envelope.

The consolidator `errorCascade_le_mainFormalError` packages all five bounds
against `mainFormalError` itself (with `ζ₃/2 ≤ mainFormalError`, as stated
in paper line 230).

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

/-- The polynomial-exponent envelope common to all cascade bounds,
`ε^(1/40000) + (d/q)^(1/40000) + exp(-k/(2560000 m²))`. See
`mainFormalError_eq_envelope` for the identification
`mainFormalError = 100000 · k² · m⁴ · mainFormalEnvelope`. -/
noncomputable def mainFormalEnvelope (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  Real.rpow eps (1 / (40000 : Error)) +
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (40000 : Error)) +
    Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ)))))

/-- `mainFormalError` factors as `100000 · k² · m⁴ · mainFormalEnvelope`. -/
theorem mainFormalError_eq_envelope (params : Parameters) (k : ℕ) (eps : Error) :
    mainFormalError params k eps =
      100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps := rfl

/-- The envelope is nonnegative whenever `ε ≥ 0`. -/
theorem mainFormalEnvelope_nonneg (params : Parameters) (k : ℕ) (eps : Error)
    (heps : 0 ≤ eps) :
    0 ≤ mainFormalEnvelope params k eps := by
  unfold mainFormalEnvelope
  refine add_nonneg (add_nonneg (Real.rpow_nonneg heps _) ?_) (Real.exp_nonneg _)
  exact Real.rpow_nonneg (by positivity) _

/-- Paper quantity `σ` (see `inductive_step.tex:189`), built from an incoming
induction-step error `ν` and the main-induction exponential decay factor. -/
noncomputable def cascadeSigma (params : Parameters) (k : ℕ) (ν : Error) : Error :=
  ((params.m : Error) ^ (2 : ℕ)) *
    (ν + Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))

/-- Paper quantity `ζ₁ = 2σ + 2·√(3ε + 2σ) + m·d/q` (see `inductive_step.tex:133`). -/
noncomputable def cascadeZeta1 (params : Parameters) (eps σ : Error) : Error :=
  2 * σ + 2 * Real.sqrt (3 * eps + 2 * σ) +
    (params.m : Error) * (params.d : Error) / (params.q : Error)

/-- Paper quantity `ζ₂ = 200·ζ₁^(1/4) + 40·ζ₁^(1/8)` (see `inductive_step.tex:149`). -/
noncomputable def cascadeZeta2 (ζ₁ : Error) : Error :=
  200 * Real.rpow ζ₁ (1 / (4 : Error)) + 40 * Real.rpow ζ₁ (1 / (8 : Error))

/-- Paper quantity `ζ₃ = 6·ζ₁ + 6·ζ₂` (see `inductive_step.tex:158`). -/
noncomputable def cascadeZeta3 (ζ₁ ζ₂ : Error) : Error :=
  6 * ζ₁ + 6 * ζ₂

/-- Paper quantity `ζ₄ = 2σ + 2·√(ζ₁ + ζ₃/2)` (see `inductive_step.tex:181`). -/
noncomputable def cascadeZeta4 (σ ζ₁ ζ₃ : Error) : Error :=
  2 * σ + 2 * Real.sqrt (ζ₁ + ζ₃ / 2)

/-- Standing numeric regime used throughout the cascade bounds: parameters
satisfy the unit scale, and `ε, d/q ∈ [0, 1]`. -/
structure CascadeHypotheses (params : Parameters) (k : ℕ) (eps : Error) : Prop where
  hk : 1 ≤ (k : Error)
  hm : 1 ≤ (params.m : Error)
  hepsNN : 0 ≤ eps
  hepsOne : eps ≤ 1
  hdq : (params.d : Error) ≤ (params.q : Error)
  hqPos : 0 < (params.q : Error)

namespace CascadeHypotheses

variable {params : Parameters} {k : ℕ} {eps : Error}
variable (h : CascadeHypotheses params k eps)

include h

/-- Non-negativity of `d/q` under the standing hypotheses. -/
theorem dqNN : 0 ≤ (params.d : Error) / (params.q : Error) :=
  div_nonneg (Nat.cast_nonneg _) h.hqPos.le

/-- `d/q ≤ 1` under the standing hypotheses. -/
theorem dqLeOne : (params.d : Error) / (params.q : Error) ≤ 1 :=
  (div_le_one h.hqPos).mpr h.hdq

/-- The envelope is nonneg. -/
theorem envelope_nonneg : 0 ≤ mainFormalEnvelope params k eps :=
  mainFormalEnvelope_nonneg params k eps h.hepsNN

/-- `1 ≤ m²`. -/
theorem m2_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
  simpa using one_le_pow₀ (n := (2 : ℕ)) h.hm

/-- `1 ≤ k²`. -/
theorem k2_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
  simpa using one_le_pow₀ (n := (2 : ℕ)) h.hk

/-- `1 ≤ m⁴`. -/
theorem m4_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  simpa using one_le_pow₀ (n := (4 : ℕ)) h.hm

/-- `m² ≤ m⁴`. -/
theorem m2_le_m4 : ((params.m : Error) ^ (2 : ℕ)) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  apply pow_le_pow_right₀ h.hm
  norm_num

/-- `k ≤ k²`. -/
theorem k_le_k2 : (k : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
  have hk_nn : 0 ≤ (k : Error) := by linarith [h.hk]
  have : (k : Error) * 1 ≤ (k : Error) * (k : Error) :=
    mul_le_mul_of_nonneg_left h.hk hk_nn
  simpa [sq] using this

/-- `m ≤ m⁴`. -/
theorem m_le_m4 : (params.m : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  have hm2_ge : (params.m : Error) ≤ ((params.m : Error) ^ (2 : ℕ)) := by
    have hm_nn : 0 ≤ (params.m : Error) := by linarith [h.hm]
    have : (params.m : Error) * 1 ≤ (params.m : Error) * (params.m : Error) :=
      mul_le_mul_of_nonneg_left h.hm hm_nn
    simpa [sq] using this
  exact hm2_ge.trans h.m2_le_m4

/-- `k m² ≤ k² m⁴`. -/
theorem km2_le_k2m4 : (k : Error) * ((params.m : Error) ^ (2 : ℕ)) ≤
    ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) :=
  mul_le_mul h.k_le_k2 h.m2_le_m4 (by positivity) (by positivity)

/-- `k² · m⁴ ≥ 1`. -/
theorem k2_m4_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) *
    ((params.m : Error) ^ (4 : ℕ)) := by
  nlinarith [h.k2_ge_one, h.m4_ge_one]

end CascadeHypotheses

/-- A paper-local envelope with exponent `1/n` and decay scale `N`. -/
private noncomputable def stepEnvelope (params : Parameters) (k : ℕ) (eps : Error)
    (n N : Error) : Error :=
  Real.rpow eps (1 / n) +
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / n) +
    Real.exp (-((k : Error) / (N * ((params.m : Error) ^ (2 : ℕ)))))

private theorem mainFormalEnvelope_eq_stepEnvelope (params : Parameters) (k : ℕ) (eps : Error) :
    mainFormalEnvelope params k eps =
      stepEnvelope params k eps (40000 : Error) (2560000 : Error) := rfl

private theorem rpow_le_of_denom_le {x : Error} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n₁ n₂ : Error} (hn₁Pos : 0 < n₁) (hn : n₁ ≤ n₂) :
    Real.rpow x (1 / n₁) ≤ Real.rpow x (1 / n₂) := by
  have hn₂Pos : 0 < n₂ := lt_of_lt_of_le hn₁Pos hn
  have hdiv : 1 / n₂ ≤ 1 / n₁ := one_div_le_one_div_of_le hn₁Pos hn
  exact Real.rpow_le_rpow_of_exponent_ge' hx hx1 (show 0 ≤ 1 / n₂ by positivity) hdiv

private theorem exp_neg_le_of_denom_ge (k : ℕ) (m : Error) (hm : 0 < m)
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

private theorem stepEnvelope_nonneg {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error} :
    0 ≤ stepEnvelope params k eps n N := by
  unfold stepEnvelope
  refine add_nonneg (add_nonneg (Real.rpow_nonneg h.hepsNN _) ?_) (Real.exp_nonneg _)
  exact Real.rpow_nonneg h.dqNN _

private theorem stepEnvelope_le_stepEnvelope {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n₁ n₂ N₁ N₂ : Error}
    (hn₁Pos : 0 < n₁) (hn : n₁ ≤ n₂) (hN₁Pos : 0 < N₁) (hN : N₁ ≤ N₂) :
    stepEnvelope params k eps n₁ N₁ ≤ stepEnvelope params k eps n₂ N₂ := by
  unfold stepEnvelope
  have hEps := rpow_le_of_denom_le h.hepsNN h.hepsOne hn₁Pos hn
  have hDq := rpow_le_of_denom_le h.dqNN h.dqLeOne hn₁Pos hn
  have hmPos : 0 < (params.m : Error) := by linarith [h.hm]
  have hExp := exp_neg_le_of_denom_ge k (params.m : Error) hmPos hN₁Pos hN
  linarith

private theorem stepEnvelope_le_mainFormalEnvelope {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error}
    (hnPos : 0 < n) (hn : n ≤ 40000) (hNPos : 0 < N) (hN : N ≤ 2560000) :
    stepEnvelope params k eps n N ≤ mainFormalEnvelope params k eps := by
  calc
    stepEnvelope params k eps n N ≤ stepEnvelope params k eps (40000 : Error) (2560000 : Error) :=
      stepEnvelope_le_stepEnvelope (h := h) (hn₁Pos := hnPos) (hn := hn)
        (hN₁Pos := hNPos) (hN := hN)
    _ = mainFormalEnvelope params k eps := by rw [mainFormalEnvelope_eq_stepEnvelope]

private theorem sqrt_add_le_add_sqrt {x y : Error} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y]

private theorem sqrt_add3_le_add3_sqrt {x y z : Error} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    Real.sqrt (x + y + z) ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
  calc
    Real.sqrt (x + y + z) = Real.sqrt ((x + y) + z) := by ring
    _ ≤ Real.sqrt (x + y) + Real.sqrt z := sqrt_add_le_add_sqrt (add_nonneg hx hy) hz
    _ ≤ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
      nlinarith [sqrt_add_le_add_sqrt hx hy, Real.sqrt_nonneg z]

private theorem sqrt_rpow_one_div {x n : Error} (hx : 0 ≤ x) (_hn : 0 < n) :
    Real.sqrt (Real.rpow x (1 / n)) = Real.rpow x (1 / (2 * n)) := by
  have hn0 : n ≠ 0 := by linarith
  rw [Real.sqrt_eq_rpow]
  calc
    Real.rpow (Real.rpow x (1 / n)) (1 / (2 : Error))
      = Real.rpow x ((1 / n) * (1 / (2 : Error))) := by
          simpa using (Real.rpow_mul hx (1 / n) (1 / (2 : Error))).symm
    _ = Real.rpow x (1 / (2 * n)) := by
      field_simp [hn0]

private theorem sqrt_exp_neg_div (k : ℕ) (m N : Error) (hm : 0 < m) (hN : 0 < N) :
    Real.sqrt (Real.exp (-((k : Error) / (N * m ^ (2 : ℕ))))) =
      Real.exp (-((k : Error) / ((2 * N) * m ^ (2 : ℕ)))) := by
  rw [← Real.exp_half]
  congr 1
  field_simp [hm.ne', hN.ne']

private theorem sqrt_stepEnvelope_le {params : Parameters} {k : ℕ} {eps : Error}
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

private theorem stepEnvelope_le_sq_stepEnvelope {params : Parameters} {k : ℕ} {eps : Error}
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

private theorem self_le_rpow_one_div {x : Error} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n : Error} (hn : 1 ≤ n) :
    x ≤ Real.rpow x (1 / n) := by
  have hnPos : 0 < n := by linarith
  have hdiv : 1 / n ≤ (1 : Error) := by
    field_simp [hnPos.ne']
    linarith
  simpa [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_ge' hx hx1 (show 0 ≤ 1 / n by positivity) hdiv)

private theorem m_le_k2m4_aux {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    (params.m : Error) ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
  calc
    (params.m : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := h.m_le_m4
    _ = 1 * ((params.m : Error) ^ (4 : ℕ)) := by ring
    _ ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
      exact mul_le_mul_of_nonneg_right h.k2_ge_one (by positivity)

private theorem dq_le_rpow2048 {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    (params.d : Error) / (params.q : Error) ≤
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) :=
  self_le_rpow_one_div h.dqNN h.dqLeOne (by norm_num)

private theorem dq_rpow2048_le_stepEnvelope2048 {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) ≤
      stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  unfold stepEnvelope
  have hepsNN' : 0 ≤ Real.rpow eps (1 / (2048 : Error)) := Real.rpow_nonneg h.hepsNN _
  have hExpNN' : 0 ≤ Real.exp (-((k : Error) / ((160000 : Error) * ((params.m : Error) ^ (2 : ℕ))))) :=
    Real.exp_nonneg _
  exact (le_add_of_nonneg_left hepsNN').trans (le_add_of_nonneg_right hExpNN')

private theorem mdq_le_k2m4_stepEnvelope2048 {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    (params.m : Error) * ((params.d : Error) / (params.q : Error)) ≤
      ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  have hTNN : 0 ≤ stepEnvelope params k eps (2048 : Error) (160000 : Error) :=
    stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hdq_to_T : (params.d : Error) / (params.q : Error) ≤ stepEnvelope params k eps (2048 : Error) (160000 : Error) :=
    (dq_le_rpow2048 h).trans (dq_rpow2048_le_stepEnvelope2048 h)
  have hmdq_to_mT : (params.m : Error) * ((params.d : Error) / (params.q : Error)) ≤
      (params.m : Error) * stepEnvelope params k eps (2048 : Error) (160000 : Error) :=
    mul_le_mul_of_nonneg_left hdq_to_T (Nat.cast_nonneg params.m)
  have hmT : (params.m : Error) * stepEnvelope params k eps (2048 : Error) (160000 : Error) ≤
      (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ))) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) :=
    mul_le_mul_of_nonneg_right (m_le_k2m4_aux (h := h)) hTNN
  exact hmdq_to_mT.trans hmT

private theorem four_mul_le_k2m4_mul {params : Parameters} {k : ℕ} {eps T : Error}
    (h : CascadeHypotheses params k eps) (hT : 0 ≤ T) :
    4 * T ≤ 4 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ))) * T := by
  have hscale : (4 : Error) ≤ 4 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ))) := by
    simpa using mul_le_mul_of_nonneg_left h.k2_m4_ge_one (by norm_num : (0 : Error) ≤ 4)
  exact mul_le_mul_of_nonneg_right hscale hT

private theorem sqrt_three_le_two : Real.sqrt (3 : Error) ≤ 2 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

private theorem sqrt20000_le_142 : Real.sqrt (20000 : Error) ≤ 142 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

private theorem sqrt20204_le_143 : Real.sqrt (20204 : Error) ≤ 143 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

private theorem sqrt150000_le_388 : Real.sqrt (150000 : Error) ≤ 388 := by
  refine (Real.sqrt_le_iff).2 ?_
  constructor <;> norm_num

private theorem two_sqrt40005_le_401 : 2 * Real.sqrt (40005 : Error) ≤ 401 := by
  have hsqrt : Real.sqrt (40005 : Error) ≤ 401 / 2 := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor <;> norm_num
  nlinarith

private theorem rpow20204_quarter_le_12 : Real.rpow (20204 : Error) (1 / (4 : Error)) ≤ 12 := by
  have hmono := Real.rpow_le_rpow (show 0 ≤ (20204 : Error) by norm_num)
    (by norm_num : (20204 : Error) ≤ (12 : Error) ^ (4 : ℕ)) (by positivity : 0 ≤ (1 / (4 : Error)))
  calc
    Real.rpow (20204 : Error) (1 / (4 : Error))
      ≤ Real.rpow ((12 : Error) ^ (4 : ℕ)) (1 / (4 : Error)) := hmono
    _ = Real.rpow (12 : Error) ((4 : Error) * (1 / (4 : Error))) := by
      symm
      exact Real.rpow_natCast_mul (by norm_num : 0 ≤ (12 : Error)) 4 (1 / (4 : Error))
    _ = (12 : Error) := by norm_num [Real.rpow_one]

private theorem rpow20204_eighth_le_4 : Real.rpow (20204 : Error) (1 / (8 : Error)) ≤ 4 := by
  have hmono := Real.rpow_le_rpow (show 0 ≤ (20204 : Error) by norm_num)
    (by norm_num : (20204 : Error) ≤ (4 : Error) ^ (8 : ℕ)) (by positivity : 0 ≤ (1 / (8 : Error)))
  calc
    Real.rpow (20204 : Error) (1 / (8 : Error))
      ≤ Real.rpow ((4 : Error) ^ (8 : ℕ)) (1 / (8 : Error)) := hmono
    _ = Real.rpow (4 : Error) ((8 : Error) * (1 / (8 : Error))) := by
      symm
      exact Real.rpow_natCast_mul (by norm_num : 0 ≤ (4 : Error)) 8 (1 / (8 : Error))
    _ = (4 : Error) := by norm_num [Real.rpow_one]

private theorem k2_rpow_quarter_le {params : Parameters} {k : ℕ} {eps : Error}
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

private theorem m4_rpow_quarter_eq {params : Parameters} :
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (4 : Error)) = (params.m : Error) := by
  calc
    Real.rpow ((params.m : Error) ^ (4 : ℕ)) (1 / (4 : Error))
      = Real.rpow (params.m : Error) ((4 : Error) * (1 / (4 : Error))) := by
        symm
        exact Real.rpow_natCast_mul (by positivity : 0 ≤ (params.m : Error)) 4 (1 / (4 : Error))
    _ = (params.m : Error) := by norm_num [Real.rpow_one]

private theorem k2_rpow_eighth_le {params : Parameters} {k : ℕ} {eps : Error}
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

private theorem m4_rpow_eighth_le {params : Parameters} {k : ℕ} {eps : Error}
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

private theorem rpow_one_four_eq_sqrt_sqrt {x : Error} (hx : 0 ≤ x) :
    Real.rpow x (1 / (4 : Error)) = Real.sqrt (Real.sqrt x) := by
  calc
    Real.rpow x (1 / (4 : Error)) = Real.rpow x ((1 / (2 : Error)) * (1 / (2 : Error))) := by norm_num
    _ = Real.rpow (Real.rpow x (1 / (2 : Error))) (1 / (2 : Error)) := by
      simpa using (Real.rpow_mul hx (1 / (2 : Error)) (1 / (2 : Error)))
    _ = Real.sqrt (Real.sqrt x) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
      rfl

private theorem rpow_one_eight_eq_sqrt_sqrt_sqrt {x : Error} (hx : 0 ≤ x) :
    Real.rpow x (1 / (8 : Error)) = Real.sqrt (Real.sqrt (Real.sqrt x)) := by
  calc
    Real.rpow x (1 / (8 : Error)) = Real.rpow x ((1 / (4 : Error)) * (1 / (2 : Error))) := by norm_num
    _ = Real.rpow (Real.rpow x (1 / (4 : Error))) (1 / (2 : Error)) := by
      simpa using (Real.rpow_mul hx (1 / (4 : Error)) (1 / (2 : Error)))
    _ = Real.sqrt (Real.sqrt (Real.sqrt x)) := by
      rw [Real.sqrt_eq_rpow, rpow_one_four_eq_sqrt_sqrt hx]
      rfl

private theorem stepEnvelope_rpow_quarter_le {params : Parameters} {k : ℕ} {eps : Error}
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

private theorem stepEnvelope_rpow_eighth_le {params : Parameters} {k : ℕ} {eps : Error}
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
    Real.rpow (stepEnvelope params k eps (2048 : Error) (160000 : Error)) (1 / (8 : Error))
      = Real.sqrt (Real.sqrt (Real.sqrt (stepEnvelope params k eps (2048 : Error) (160000 : Error)))) :=
        rpow_one_eight_eq_sqrt_sqrt_sqrt hnn
    _ ≤ Real.sqrt (Real.sqrt (stepEnvelope params k eps (4096 : Error) (320000 : Error))) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h1)
    _ ≤ Real.sqrt (stepEnvelope params k eps (8192 : Error) (640000 : Error)) :=
      Real.sqrt_le_sqrt h2
    _ ≤ stepEnvelope params k eps (16384 : Error) (1280000 : Error) := h3

private theorem sqrt_scaled_stepEnvelope_le {params : Parameters} {k : ℕ} {eps x C n N : Error}
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
    Real.sqrt x ≤ Real.sqrt (C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) * E ^ (2 : ℕ)) := hsqrt
    _ = Real.sqrt (C * (u ^ (2 : ℕ))) := by
      rw [show C * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) * E ^ (2 : ℕ) = C * (u ^ (2 : ℕ)) by
        dsimp [u]
        ring]
    _ = Real.sqrt C * u := by
      rw [Real.sqrt_mul hC, Real.sqrt_sq_eq_abs, abs_of_nonneg huNN]
    _ = Real.sqrt C * (k : Error) * ((params.m : Error) ^ (2 : ℕ)) *
          stepEnvelope params k eps (2 * n) (2 * N) := by
      simp [u, E]
      ring

private theorem cascadeSigma_tight_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeSigma params k ν ≤
      10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (1024 : Error) (80000 : Error) := by
  unfold cascadeSigma stepEnvelope
  set m2 : Error := (params.m : Error) ^ (2 : ℕ) with hm2_def
  set m4 : Error := (params.m : Error) ^ (4 : ℕ) with hm4_def
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  have hm2NN : 0 ≤ m2 := by positivity
  have hk2_ge_one : (1 : Error) ≤ k2 := h.k2_ge_one
  have hm2_le_m4 : m2 ≤ m4 := h.m2_le_m4
  have hm2_sq_m4 : m2 * m2 = m4 := by
    simp only [hm2_def, hm4_def]
    ring
  have hStep1 :
      m2 * ν ≤ 10000 * k2 * m4 *
        (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
    have hreorder :
        m2 * (10000 * k2 * m2 *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) =
          10000 * k2 * (m2 * m2) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
      ring
    calc
      m2 * ν
          ≤ m2 * (10000 * k2 * m2 *
              (Real.rpow eps (1 / (1024 : Error)) +
                Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :=
            mul_le_mul_of_nonneg_left hν hm2NN
      _ = 10000 * k2 * (m2 * m2) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := hreorder
      _ = 10000 * k2 * m4 *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by rw [hm2_sq_m4]
  have hScaleGeOne : (1 : Error) ≤ 10000 * k2 := by
    nlinarith [hk2_ge_one]
  have hm2_le_10k2m4 : m2 ≤ 10000 * k2 * m4 := by
    calc
      m2 ≤ m4 := hm2_le_m4
      _ ≤ (10000 * k2) * m4 := by
        nlinarith [hScaleGeOne, show 0 ≤ m4 by positivity]
      _ = 10000 * k2 * m4 := by ring
  have hStep2 :
      m2 * Real.exp (-((k : Error) / (80000 * m2))) ≤
        10000 * k2 * m4 * Real.exp (-((k : Error) / (80000 * m2))) := by
    have hExpNN : 0 ≤ Real.exp (-((k : Error) / (80000 * m2))) := Real.exp_nonneg _
    exact mul_le_mul_of_nonneg_right hm2_le_10k2m4 hExpNN
  have hExpand : m2 * (ν + Real.exp (-((k : Error) / (80000 * m2)))) =
      m2 * ν + m2 * Real.exp (-((k : Error) / (80000 * m2))) := by ring
  rw [hExpand]
  calc
    m2 * ν + m2 * Real.exp (-((k : Error) / (80000 * m2)))
        ≤ 10000 * k2 * m4 *
              (Real.rpow eps (1 / (1024 : Error)) +
                Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) +
            10000 * k2 * m4 * Real.exp (-((k : Error) / (80000 * m2))) := by
          nlinarith [hStep1, hStep2]
    _ = 10000 * k2 * m4 *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) +
            Real.exp (-((k : Error) / (80000 * m2)))) := by ring

/-- **Paper lines 189–193.** The paper's bound for `σ` is absorbed by
`10000 · k² · m⁴ · mainFormalEnvelope`. -/
theorem sigma_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeSigma params k ν ≤
      10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps := by
  have hTight := cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hEnv : stepEnvelope params k eps (1024 : Error) (80000 : Error) ≤
      mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (1024 : Error)) (N := (80000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hCoeffNN : 0 ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  calc
    cascadeSigma params k ν
      ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          stepEnvelope params k eps (1024 : Error) (80000 : Error) := hTight
    _ ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_left hEnv hCoeffNN

private theorem cascadeSigma_nonneg {params : Parameters} {k : ℕ} {ν : Error}
    (hνNN : 0 ≤ ν) :
    0 ≤ cascadeSigma params k ν := by
  unfold cascadeSigma
  positivity

private theorem cascadeZeta1_nonneg {params : Parameters} {k : ℕ} {eps ν : Error}
    (h : CascadeHypotheses params k eps) (hνNN : 0 ≤ ν) :
    0 ≤ cascadeZeta1 params eps (cascadeSigma params k ν) := by
  have hσNN := cascadeSigma_nonneg (params := params) (k := k) (ν := ν) hνNN
  unfold cascadeZeta1
  positivity [hσNN, h.hepsNN, h.dqNN]

private theorem cascadeZeta1_bound_special {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hkm1 : k = 1 ∧ params.m = 1) :
    cascadeZeta1 params eps (cascadeSigma params k ν) ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  rcases hkm1 with ⟨rfl, hm1⟩
  have hm_cast : (params.m : Error) = 1 := by exact_mod_cast hm1
  set a : Error := Real.rpow eps (1 / (2048 : Error))
  set b : Error := Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error))
  set c : Error := Real.exp (-(1 : Error) / (160000 : Error))
  have heps1024 : Real.rpow eps (1 / (1024 : Error)) ≤ a := by
    simpa [a] using rpow_le_of_denom_le h.hepsNN h.hepsOne (n₁ := (1024 : Error))
      (n₂ := (2048 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
  have hdq1024 : Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) ≤ b := by
    simpa [b] using rpow_le_of_denom_le h.dqNN h.dqLeOne (n₁ := (1024 : Error))
      (n₂ := (2048 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
  have hνab : ν ≤ 10000 * (a + b) := by
    calc
      ν ≤ 10000 * (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
            simpa [hm_cast] using hν
      _ ≤ 10000 * (a + b) := by nlinarith [heps1024, hdq1024]
  have hExp80000_le_c : Real.exp (-((1 : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤ c := by
    calc
      Real.exp (-((1 : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))
          = Real.exp (-(1 : Error) / (80000 : Error)) := by norm_num [hm_cast]
      _ ≤ Real.exp (-(1 : Error) / (160000 : Error)) := by
            exact Real.exp_le_exp.mpr (by norm_num)
      _ = c := by rfl
  have hσab : cascadeSigma params 1 ν ≤ 10000 * (a + b) + c := by
    have htmp : ν + Real.exp (-((1 : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
        10000 * (a + b) + c := by
      nlinarith [hνab, hExp80000_le_c]
    simpa [cascadeSigma, hm_cast] using htmp
  have ha_le_one : a ≤ 1 := by
    unfold a
    exact Real.rpow_le_one h.hepsNN h.hepsOne (by positivity)
  have hb_le_one : b ≤ 1 := by
    unfold b
    exact Real.rpow_le_one h.dqNN h.dqLeOne (by positivity)
  have hc_le_one : c ≤ 1 := by
    unfold c
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have hσ_le_20001 : cascadeSigma params 1 ν ≤ 20001 := by
    nlinarith [hσab, ha_le_one, hb_le_one, hc_le_one]
  have hsqrt_le_401 : 2 * Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) ≤ 401 := by
    have hinside : 3 * eps + 2 * cascadeSigma params 1 ν ≤ 40005 := by
      nlinarith [h.hepsOne, hσ_le_20001]
    have hsqrt : Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) ≤ Real.sqrt (40005 : Error) :=
      Real.sqrt_le_sqrt hinside
    nlinarith [hsqrt, two_sqrt40005_le_401]
  have hdq_le_b : (params.d : Error) / (params.q : Error) ≤ b := by
    exact self_le_rpow_one_div h.dqNN h.dqLeOne (by norm_num)
  have hc_ge_quarter : (1 / 4 : Error) ≤ c := by
    have hexp_neg_one : Real.exp (- (1 : Error)) ≤ c := by
      unfold c
      exact Real.exp_le_exp.mpr (by norm_num)
    have hquarter_lt : (1 / 4 : Error) < Real.exp (- (1 : Error)) := by
      linarith [Real.exp_neg_one_gt_d9]
    exact hquarter_lt.le.trans hexp_neg_one
  have hconst : (401 : Error) ≤ 20202 * c := by
    nlinarith [hc_ge_quarter]
  have htarget :
      2 * cascadeSigma params 1 ν + 2 * Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) +
          (params.d : Error) / (params.q : Error)
        ≤ 20204 * (a + b + c) := by
    have htwoσ : 2 * cascadeSigma params 1 ν ≤ 20000 * (a + b) + 2 * c := by
      nlinarith [hσab]
    calc
      2 * cascadeSigma params 1 ν + 2 * Real.sqrt (3 * eps + 2 * cascadeSigma params 1 ν) +
          (params.d : Error) / (params.q : Error)
          ≤ (20000 * (a + b) + 2 * c) + 401 + b := by
            nlinarith [htwoσ, hsqrt_le_401, hdq_le_b]
      _ ≤ 20204 * (a + b + c) := by
            nlinarith [hconst,
              show 0 ≤ a by
                unfold a
                exact Real.rpow_nonneg h.hepsNN _,
              show 0 ≤ b by
                unfold b
                exact Real.rpow_nonneg h.dqNN _]
  have hEnv : stepEnvelope params 1 eps (2048 : Error) (160000 : Error) = a + b + c := by
    unfold stepEnvelope a b c
    norm_num [hm_cast]
  simpa [cascadeZeta1, hm_cast, hEnv] using htarget

private theorem cascadeZeta1_bound_general {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hkm1 : ¬ (k = 1 ∧ params.m = 1)) :
    cascadeZeta1 params eps (cascadeSigma params k ν) ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m2 : Error := (params.m : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set S : Error := stepEnvelope params k eps (1024 : Error) (80000 : Error)
  set T : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set σ : Error := cascadeSigma params k ν
  have hσtight : σ ≤ 10000 * k2 * m4 * S := by
    simpa [σ, k2, m4, S] using cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hST : S ≤ T := by
    simpa [S, T] using stepEnvelope_le_stepEnvelope (h := h) (n₁ := (1024 : Error))
      (n₂ := (2048 : Error)) (N₁ := (80000 : Error)) (N₂ := (160000 : Error))
      (hn₁Pos := by norm_num) (hn := by norm_num) (hN₁Pos := by norm_num) (hN := by norm_num)
  have hσtoT : σ ≤ 10000 * k2 * m4 * T := by
    calc
      σ ≤ 10000 * k2 * m4 * S := hσtight
      _ ≤ 10000 * k2 * m4 * T := by
        exact mul_le_mul_of_nonneg_left hST (by positivity)
  have htwoσ : 2 * σ ≤ 20000 * k2 * m4 * T := by
    nlinarith [hσtoT]
  have hTNN : 0 ≤ T := by
    simpa [T] using stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hSNN : 0 ≤ S := by
    simpa [S] using stepEnvelope_nonneg (h := h) (n := (1024 : Error)) (N := (80000 : Error))
  have hEpsTerm : Real.rpow eps (1 / (2048 : Error)) ≤ T := by
    unfold T stepEnvelope
    have hdqNN' : 0 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) :=
      Real.rpow_nonneg h.dqNN _
    have hExpNN' : 0 ≤ Real.exp (-((k : Error) / ((160000 : Error) * ((params.m : Error) ^ (2 : ℕ))))) :=
      Real.exp_nonneg _
    nlinarith
  have hsqrt_eps : Real.sqrt eps ≤ Real.rpow eps (1 / (2048 : Error)) := by
    calc
      Real.sqrt eps = Real.rpow eps (1 / (2 : Error)) := by simpa using (Real.sqrt_eq_rpow eps)
      _ ≤ Real.rpow eps (1 / (2048 : Error)) :=
        rpow_le_of_denom_le h.hepsNN h.hepsOne (n₁ := (2 : Error)) (n₂ := (2048 : Error))
          (hn₁Pos := by norm_num) (hn := by norm_num)
  have hsqrt3eps : Real.sqrt (3 * eps) ≤ 2 * T := by
    calc
      Real.sqrt (3 * eps) = Real.sqrt (3 : Error) * Real.sqrt eps := by
        rw [Real.sqrt_mul (by norm_num)]
      _ ≤ 2 * Real.sqrt eps := by
        exact mul_le_mul_of_nonneg_right sqrt_three_le_two (Real.sqrt_nonneg _)
      _ ≤ 2 * Real.rpow eps (1 / (2048 : Error)) :=
        mul_le_mul_of_nonneg_left hsqrt_eps (by norm_num)
      _ ≤ 2 * T := mul_le_mul_of_nonneg_left hEpsTerm (by norm_num)
  have hsqrtScaled : Real.sqrt (20000 * k2 * m4 * S) ≤
      Real.sqrt (20000 : Error) * (k : Error) * m2 * T := by
    simpa [k2, m2, m4, S, T,
      show (2 : Error) * 1024 = 2048 by norm_num,
      show (2 : Error) * 80000 = 160000 by norm_num] using
      sqrt_scaled_stepEnvelope_le (h := h)
        (x := 20000 * k2 * m4 * S) (C := (20000 : Error))
        (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
  have hsqrtScaled142 : Real.sqrt (20000 * k2 * m4 * S) ≤ 142 * (k : Error) * m2 * T := by
    calc
      Real.sqrt (20000 * k2 * m4 * S)
        ≤ Real.sqrt (20000 : Error) * (k : Error) * m2 * T := hsqrtScaled
      _ ≤ 142 * (k : Error) * m2 * T := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_right sqrt20000_le_142 (show 0 ≤ (k : Error) * m2 * T by positivity [hTNN])
  have hsqrtTmp : Real.sqrt (3 * eps + 2 * σ) ≤
      Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S) := by
    have harg : 3 * eps + 2 * σ ≤ 3 * eps + 20000 * k2 * m4 * S := by
      nlinarith [hσtight, hSNN]
    calc
      Real.sqrt (3 * eps + 2 * σ)
        ≤ Real.sqrt (3 * eps + 20000 * k2 * m4 * S) := Real.sqrt_le_sqrt harg
      _ ≤ Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S) :=
        sqrt_add_le_add_sqrt (by nlinarith [h.hepsNN]) (by positivity [hSNN])
  have hkm2_ge_two : (2 : Error) ≤ (k : Error) * m2 := by
    by_cases hk1 : k = 1
    · have hmNe : params.m ≠ 1 := by
        intro hmEq
        exact hkm1 ⟨hk1, hmEq⟩
      have hmNat2 : 2 ≤ params.m := by
        have hmNat1 : 1 ≤ params.m := by exact_mod_cast h.hm
        omega
      have hm_ge_two : (2 : Error) ≤ (params.m : Error) := by exact_mod_cast hmNat2
      have hm2_ge_two : (2 : Error) ≤ m2 := by
        dsimp [m2]
        nlinarith [hm_ge_two]
      simpa [hk1] using hm2_ge_two
    · have hkNat2 : 2 ≤ k := by
        have hkNat1 : 1 ≤ k := by exact_mod_cast h.hk
        omega
      have hk_ge_two : (2 : Error) ≤ (k : Error) := by exact_mod_cast hkNat2
      nlinarith [hk_ge_two, h.m2_ge_one]
  have hkm2NN : 0 ≤ (k : Error) * m2 := by positivity
  have hkm2_sq : (((k : Error) * m2) ^ (2 : ℕ)) = k2 * m4 := by
    dsimp [k2, m2, m4]
    ring
  have hCoeffDirect : (284 : Error) * ((k : Error) * m2) ≤ 199 * k2 * m4 := by
    have h284 : (284 : Error) ≤ 199 * ((k : Error) * m2) := by
      nlinarith [hkm2_ge_two]
    have hmul := mul_le_mul_of_nonneg_right h284 hkm2NN
    calc
      (284 : Error) * ((k : Error) * m2) ≤ (199 * ((k : Error) * m2)) * ((k : Error) * m2) := by
        simpa [mul_assoc] using hmul
      _ = 199 * (((k : Error) * m2) ^ (2 : ℕ)) := by ring
      _ = 199 * k2 * m4 := by rw [hkm2_sq]; ring
  have hsqrtBig : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ 199 * k2 * m4 * T := by
    have htmp1' : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ 2 * (142 * (k : Error) * m2 * T) :=
      mul_le_mul_of_nonneg_left hsqrtScaled142 (by norm_num : (0 : Error) ≤ 2)
    have htmp1b : 2 * (142 * (k : Error) * m2 * T) = (284 * ((k : Error) * m2)) * T := by
      ring
    have htmp1 : 2 * Real.sqrt (20000 * k2 * m4 * S) ≤ (284 * ((k : Error) * m2)) * T := by
      exact htmp1'.trans_eq htmp1b
    have htmp2 : (284 * ((k : Error) * m2)) * T ≤ (199 * k2 * m4) * T :=
      mul_le_mul_of_nonneg_right hCoeffDirect hTNN
    have htmp3 : (199 * k2 * m4) * T = 199 * k2 * m4 * T := by ring
    exact htmp1.trans <| htmp2.trans_eq htmp3
  have hsqrt3Term : 2 * Real.sqrt (3 * eps) ≤ 4 * T := by
    have htmp : 2 * Real.sqrt (3 * eps) ≤ 2 * (2 * T) :=
      mul_le_mul_of_nonneg_left hsqrt3eps (by norm_num : (0 : Error) ≤ 2)
    have hEq : 2 * (2 * T) = 4 * T := by ring
    exact htmp.trans_eq hEq
  have hsqrtTerm : 2 * Real.sqrt (3 * eps + 2 * σ) ≤ 4 * T + 199 * k2 * m4 * T := by
    have hsqrtTmp2' : 2 * Real.sqrt (3 * eps + 2 * σ) ≤ 2 *
        (Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S)) :=
      mul_le_mul_of_nonneg_left hsqrtTmp (by norm_num : (0 : Error) ≤ 2)
    have hEq : 2 *
        (Real.sqrt (3 * eps) + Real.sqrt (20000 * k2 * m4 * S)) =
        2 * Real.sqrt (3 * eps) + 2 * Real.sqrt (20000 * k2 * m4 * S) := by ring
    have hsqrtTmp2 : 2 * Real.sqrt (3 * eps + 2 * σ) ≤
        2 * Real.sqrt (3 * eps) + 2 * Real.sqrt (20000 * k2 * m4 * S) := by
      exact hsqrtTmp2'.trans_eq hEq
    exact hsqrtTmp2.trans (add_le_add hsqrt3Term hsqrtBig)
  have hmdq_to_k2m4T : (params.m : Error) * ((params.d : Error) / (params.q : Error)) ≤ k2 * m4 * T := by
    dsimp [k2, m4, T]
    exact mdq_le_k2m4_stepEnvelope2048 (h := h)
  have hfourT : 4 * T ≤ 4 * (k2 * m4) * T := by
    dsimp [k2, m4]
    exact four_mul_le_k2m4_mul (h := h) hTNN
  rw [show cascadeZeta1 params eps σ =
      2 * σ + 2 * Real.sqrt (3 * eps + 2 * σ) +
        (params.m : Error) * (params.d : Error) / (params.q : Error) by rfl]
  have hmdq_to_k2m4T' : (params.m : Error) * (params.d : Error) / (params.q : Error) ≤ k2 * m4 * T := by
    calc
      (params.m : Error) * (params.d : Error) / (params.q : Error)
        = (params.m : Error) * ((params.d : Error) / (params.q : Error)) := by ring
      _ ≤ k2 * m4 * T := hmdq_to_k2m4T
  calc
    2 * σ + 2 * Real.sqrt (3 * eps + 2 * σ) +
        (params.m : Error) * (params.d : Error) / (params.q : Error)
      ≤ (20000 * k2 * m4 * T + (4 * T + 199 * k2 * m4 * T)) + k2 * m4 * T :=
          add_le_add (add_le_add htwoσ hsqrtTerm) hmdq_to_k2m4T'
    _ = 20000 * k2 * m4 * T + 4 * T + 199 * k2 * m4 * T + k2 * m4 * T := by ring
    _ = (20000 * k2 * m4 * T + 4 * T) + (199 * k2 * m4 * T + k2 * m4 * T) := by ring
    _ ≤ (20000 * k2 * m4 * T + 4 * (k2 * m4) * T) +
          (199 * k2 * m4 * T + k2 * m4 * T) :=
        add_le_add (add_le_add le_rfl hfourT) le_rfl
    _ = 20204 * k2 * m4 * T := by ring

private theorem cascadeZeta1_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeZeta1 params eps (cascadeSigma params k ν) ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error) := by
  by_cases hkm1 : k = 1 ∧ params.m = 1
  · exact cascadeZeta1_bound_special (h := h) (ν := ν) hν hkm1
  · exact cascadeZeta1_bound_general (h := h) (ν := ν) hν hkm1
/-- **Paper lines 196–201.** The concrete `ζ₁` built from `σ = cascadeSigma params k ν`
is absorbed by `mainFormalError`. -/
theorem zeta1_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν) :
    cascadeZeta1 params eps σ ≤ mainFormalError params k eps := by
  rw [hσEq, mainFormalError_eq_envelope]
  have hζ₁ := cascadeZeta1_bound (h := h) (ν := ν) hν
  have hTightEnvelope :
      stepEnvelope params k eps (2048 : Error) (160000 : Error) ≤ mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (2048 : Error)) (N := (160000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  have hCoeffNN : 0 ≤ 20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  refine hζ₁.trans ?_
  calc
    20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (2048 : Error) (160000 : Error)
      ≤ 20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_left hTightEnvelope hCoeffNN
    _ = (20204 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps := by ring
    _ ≤ (100000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (20204 : Error) ≤ 100000) hk2m4NN) hENN
    _ = 100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps := by ring

private theorem cascadeZeta2_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeZeta2 (cascadeZeta1 params eps (cascadeSigma params k ν)) ≤
      2560 * (k : Error) * (params.m : Error) *
        stepEnvelope params k eps (16384 : Error) (1280000 : Error) := by
  set Z1 : Error := cascadeZeta1 params eps (cascadeSigma params k ν)
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set E2048 : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set E8192 : Error := stepEnvelope params k eps (8192 : Error) (640000 : Error)
  set E16384 : Error := stepEnvelope params k eps (16384 : Error) (1280000 : Error)
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [Z1, k2, m4, E2048] using cascadeZeta1_bound (h := h) (ν := ν) hν
  have hZ1NN : 0 ≤ Z1 := by
    simpa [Z1] using cascadeZeta1_nonneg (h := h) (ν := ν) hνNN
  have hE2048NN : 0 ≤ E2048 := by
    simpa [E2048] using stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hE8192 : E8192 ≤ E16384 := by
    simpa [E8192, E16384] using stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (8192 : Error)) (n₂ := (16384 : Error)) (N₁ := (640000 : Error))
      (N₂ := (1280000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hQuarterRoot : Real.rpow Z1 (1 / (4 : Error)) ≤ 12 * (k : Error) * (params.m : Error) * E8192 := by
    set A : Error := Real.rpow (20204 : Error) (1 / (4 : Error))
    set B : Error := Real.rpow k2 (1 / (4 : Error))
    set C : Error := Real.rpow m4 (1 / (4 : Error))
    set D : Error := Real.rpow E2048 (1 / (4 : Error))
    have hA : A ≤ 12 := by simpa [A] using rpow20204_quarter_le_12
    have hB : B ≤ (k : Error) := by simpa [B, k2] using k2_rpow_quarter_le (h := h)
    have hC : C ≤ (params.m : Error) := by
      simpa [C, m4] using (m4_rpow_quarter_eq (params := params)).le
    have hD : D ≤ E8192 := by simpa [D, E2048, E8192] using stepEnvelope_rpow_quarter_le (h := h)
    have hAnn : 0 ≤ A := by
      simpa [A] using Real.rpow_nonneg (by norm_num : 0 ≤ (20204 : Error)) (1 / (4 : Error))
    have hBnn : 0 ≤ B := by
      simpa [B] using Real.rpow_nonneg (show 0 ≤ k2 by positivity) (1 / (4 : Error))
    have hCnn : 0 ≤ C := by
      simpa [C] using Real.rpow_nonneg (show 0 ≤ m4 by positivity) (1 / (4 : Error))
    have hDnn : 0 ≤ D := by
      simpa [D] using Real.rpow_nonneg hE2048NN (1 / (4 : Error))
    have hAB : A * B ≤ 12 * (k : Error) := by
      exact mul_le_mul hA hB hBnn (by positivity)
    have hABC : A * B * C ≤ 12 * (k : Error) * (params.m : Error) := by
      exact mul_le_mul hAB hC hCnn (by positivity)
    have hABCD : A * B * C * D ≤ 12 * (k : Error) * (params.m : Error) * E8192 := by
      exact mul_le_mul hABC hD hDnn (by positivity)
    have hsplit1 : Real.rpow (((20204 : Error) * k2) * (m4 * E2048)) (1 / (4 : Error)) =
        Real.rpow ((20204 : Error) * k2) (1 / (4 : Error)) * Real.rpow (m4 * E2048) (1 / (4 : Error)) := by
      simpa using (Real.mul_rpow (x := ((20204 : Error) * k2)) (y := (m4 * E2048))
        (z := (1 / (4 : Error))) (by positivity) (by positivity [hE2048NN]))
    have hsplit2a : Real.rpow ((20204 : Error) * k2) (1 / (4 : Error)) =
        Real.rpow (20204 : Error) (1 / (4 : Error)) * Real.rpow k2 (1 / (4 : Error)) := by
      simpa using (Real.mul_rpow (x := (20204 : Error)) (y := k2) (z := (1 / (4 : Error)))
        (by positivity) (by positivity))
    have hsplit2b : Real.rpow (m4 * E2048) (1 / (4 : Error)) =
        Real.rpow m4 (1 / (4 : Error)) * Real.rpow E2048 (1 / (4 : Error)) := by
      simpa using (Real.mul_rpow (x := m4) (y := E2048) (z := (1 / (4 : Error)))
        (by positivity) hE2048NN)
    have hFactor : Real.rpow (20204 * k2 * m4 * E2048) (1 / (4 : Error)) = A * B * C * D := by
      calc
        Real.rpow (20204 * k2 * m4 * E2048) (1 / (4 : Error))
            = Real.rpow (((20204 : Error) * k2) * (m4 * E2048)) (1 / (4 : Error)) := by
                congr 1
                ring
        _ = Real.rpow ((20204 : Error) * k2) (1 / (4 : Error)) * Real.rpow (m4 * E2048) (1 / (4 : Error)) := hsplit1
        _ = (Real.rpow (20204 : Error) (1 / (4 : Error)) * Real.rpow k2 (1 / (4 : Error))) *
              (Real.rpow m4 (1 / (4 : Error)) * Real.rpow E2048 (1 / (4 : Error))) := by
              rw [hsplit2a, hsplit2b]
        _ = A * B * C * D := by simp [A, B, C, D, mul_assoc, mul_left_comm, mul_comm]
    calc
      Real.rpow Z1 (1 / (4 : Error))
        ≤ Real.rpow (20204 * k2 * m4 * E2048) (1 / (4 : Error)) :=
          Real.rpow_le_rpow hZ1NN hZ1 (by positivity)
      _ = A * B * C * D := hFactor
      _ ≤ 12 * (k : Error) * (params.m : Error) * E8192 := by simpa [mul_assoc] using hABCD
  have hQuarterRoot' : Real.rpow Z1 (1 / (4 : Error)) ≤ 12 * (k : Error) * (params.m : Error) * E16384 := by
    calc
      Real.rpow Z1 (1 / (4 : Error)) ≤ 12 * (k : Error) * (params.m : Error) * E8192 := hQuarterRoot
      _ ≤ 12 * (k : Error) * (params.m : Error) * E16384 :=
        mul_le_mul_of_nonneg_left hE8192 (by positivity)
  have hEighthRoot : Real.rpow Z1 (1 / (8 : Error)) ≤ 4 * (k : Error) * (params.m : Error) * E16384 := by
    set A : Error := Real.rpow (20204 : Error) (1 / (8 : Error))
    set B : Error := Real.rpow k2 (1 / (8 : Error))
    set C : Error := Real.rpow m4 (1 / (8 : Error))
    set D : Error := Real.rpow E2048 (1 / (8 : Error))
    have hA : A ≤ 4 := by simpa [A] using rpow20204_eighth_le_4
    have hB : B ≤ (k : Error) := by simpa [B, k2] using k2_rpow_eighth_le (h := h)
    have hC : C ≤ (params.m : Error) := by simpa [C, m4] using m4_rpow_eighth_le (h := h)
    have hD : D ≤ E16384 := by simpa [D, E2048, E16384] using stepEnvelope_rpow_eighth_le (h := h)
    have hAnn : 0 ≤ A := by
      simpa [A] using Real.rpow_nonneg (by norm_num : 0 ≤ (20204 : Error)) (1 / (8 : Error))
    have hBnn : 0 ≤ B := by
      simpa [B] using Real.rpow_nonneg (show 0 ≤ k2 by positivity) (1 / (8 : Error))
    have hCnn : 0 ≤ C := by
      simpa [C] using Real.rpow_nonneg (show 0 ≤ m4 by positivity) (1 / (8 : Error))
    have hDnn : 0 ≤ D := by
      simpa [D] using Real.rpow_nonneg hE2048NN (1 / (8 : Error))
    have hAB : A * B ≤ 4 * (k : Error) := by
      exact mul_le_mul hA hB hBnn (by positivity)
    have hABC : A * B * C ≤ 4 * (k : Error) * (params.m : Error) := by
      exact mul_le_mul hAB hC hCnn (by positivity)
    have hABCD : A * B * C * D ≤ 4 * (k : Error) * (params.m : Error) * E16384 := by
      exact mul_le_mul hABC hD hDnn (by positivity)
    have hsplit1 : Real.rpow (((20204 : Error) * k2) * (m4 * E2048)) (1 / (8 : Error)) =
        Real.rpow ((20204 : Error) * k2) (1 / (8 : Error)) * Real.rpow (m4 * E2048) (1 / (8 : Error)) := by
      simpa using (Real.mul_rpow (x := ((20204 : Error) * k2)) (y := (m4 * E2048))
        (z := (1 / (8 : Error))) (by positivity) (by positivity [hE2048NN]))
    have hsplit2a : Real.rpow ((20204 : Error) * k2) (1 / (8 : Error)) =
        Real.rpow (20204 : Error) (1 / (8 : Error)) * Real.rpow k2 (1 / (8 : Error)) := by
      simpa using (Real.mul_rpow (x := (20204 : Error)) (y := k2) (z := (1 / (8 : Error)))
        (by positivity) (by positivity))
    have hsplit2b : Real.rpow (m4 * E2048) (1 / (8 : Error)) =
        Real.rpow m4 (1 / (8 : Error)) * Real.rpow E2048 (1 / (8 : Error)) := by
      simpa using (Real.mul_rpow (x := m4) (y := E2048) (z := (1 / (8 : Error)))
        (by positivity) hE2048NN)
    have hFactor : Real.rpow (20204 * k2 * m4 * E2048) (1 / (8 : Error)) = A * B * C * D := by
      calc
        Real.rpow (20204 * k2 * m4 * E2048) (1 / (8 : Error))
            = Real.rpow (((20204 : Error) * k2) * (m4 * E2048)) (1 / (8 : Error)) := by
                congr 1
                ring
        _ = Real.rpow ((20204 : Error) * k2) (1 / (8 : Error)) * Real.rpow (m4 * E2048) (1 / (8 : Error)) := hsplit1
        _ = (Real.rpow (20204 : Error) (1 / (8 : Error)) * Real.rpow k2 (1 / (8 : Error))) *
              (Real.rpow m4 (1 / (8 : Error)) * Real.rpow E2048 (1 / (8 : Error))) := by
              rw [hsplit2a, hsplit2b]
        _ = A * B * C * D := by simp [A, B, C, D, mul_assoc, mul_left_comm, mul_comm]
    calc
      Real.rpow Z1 (1 / (8 : Error))
        ≤ Real.rpow (20204 * k2 * m4 * E2048) (1 / (8 : Error)) :=
          Real.rpow_le_rpow hZ1NN hZ1 (by positivity)
      _ = A * B * C * D := hFactor
      _ ≤ 4 * (k : Error) * (params.m : Error) * E16384 := by simpa [mul_assoc] using hABCD
  unfold cascadeZeta2
  calc
    200 * Real.rpow Z1 (1 / (4 : Error)) + 40 * Real.rpow Z1 (1 / (8 : Error))
      ≤ 200 * (12 * (k : Error) * (params.m : Error) * E16384) +
          40 * (4 * (k : Error) * (params.m : Error) * E16384) := by
            nlinarith [hQuarterRoot', hEighthRoot]
    _ = 2560 * (k : Error) * (params.m : Error) * E16384 := by ring

/-- **Paper lines 205–212.** The concrete `ζ₂` built from `ζ₁ = cascadeZeta1 params eps σ`
and `σ = cascadeSigma params k ν` is absorbed by `mainFormalError`. -/
theorem zeta2_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ) :
    cascadeZeta2 ζ₁ ≤ mainFormalError params k eps := by
  rw [hζ₁Eq, hσEq, mainFormalError_eq_envelope]
  have hζ₂ := cascadeZeta2_bound (h := h) (ν := ν) hνNN hν
  have hTightEnvelope :
      stepEnvelope params k eps (16384 : Error) (1280000 : Error) ≤ mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hm_nn : 0 ≤ (params.m : Error) := by linarith [h.hm]
  have hk_le : (k : Error) ≤ ((k : Error) ^ (2 : ℕ)) := h.k_le_k2
  have hm_le : (params.m : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := h.m_le_m4
  have hkm_le : (k : Error) * (params.m : Error) ≤
      ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) :=
    mul_le_mul hk_le hm_le hm_nn (by positivity)
  have hCoeffNN : 0 ≤ 2560 * (k : Error) * (params.m : Error) := by positivity
  have hk2m4_nn : (0 : Error) ≤
      ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  refine hζ₂.trans ?_
  calc
    2560 * (k : Error) * (params.m : Error) *
        stepEnvelope params k eps (16384 : Error) (1280000 : Error)
      ≤ 2560 * (k : Error) * (params.m : Error) * mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_left hTightEnvelope hCoeffNN
    _ = (2560 * ((k : Error) * (params.m : Error))) *
          mainFormalEnvelope params k eps := by ring
    _ ≤ (2560 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hkm_le (by norm_num)) hENN
    _ ≤ (100000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (2560 : Error) ≤ 100000) hk2m4_nn) hENN
    _ = 100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps := by ring

private theorem cascadeZeta3_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeZeta3
        (cascadeZeta1 params eps (cascadeSigma params k ν))
        (cascadeZeta2 (cascadeZeta1 params eps (cascadeSigma params k ν))) ≤
      150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (16384 : Error) (1280000 : Error) := by
  set Z1 : Error := cascadeZeta1 params eps (cascadeSigma params k ν)
  set Z2 : Error := cascadeZeta2 Z1
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set E2048 : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set E16384 : Error := stepEnvelope params k eps (16384 : Error) (1280000 : Error)
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [Z1, k2, m4, E2048] using cascadeZeta1_bound (h := h) (ν := ν) hν
  have hE2048 : E2048 ≤ E16384 := by
    simpa [E2048, E16384] using stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (2048 : Error)) (n₂ := (16384 : Error)) (N₁ := (160000 : Error))
      (N₂ := (1280000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hZ1' : Z1 ≤ 20204 * k2 * m4 * E16384 := by
    calc
      Z1 ≤ 20204 * k2 * m4 * E2048 := hZ1
      _ ≤ 20204 * k2 * m4 * E16384 :=
        mul_le_mul_of_nonneg_left hE2048 (by positivity)
  have hZ2 : Z2 ≤ 2560 * (k : Error) * (params.m : Error) * E16384 := by
    simpa [Z1, Z2, E16384] using cascadeZeta2_bound (h := h) (ν := ν) hνNN hν
  have hE16384NN : 0 ≤ E16384 := by
    simpa [E16384] using stepEnvelope_nonneg (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
  have hZ2' : Z2 ≤ 2560 * k2 * m4 * E16384 := by
    have hkm_le : (k : Error) * (params.m : Error) ≤ k2 * m4 := by
      calc
        (k : Error) * (params.m : Error)
          ≤ (k : Error) * ((params.m : Error) ^ (4 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left h.m_le_m4 (by positivity)
        _ ≤ k2 * m4 := by
            exact mul_le_mul_of_nonneg_right h.k_le_k2 (by positivity)
    have hScale : 2560 * ((k : Error) * (params.m : Error)) ≤ 2560 * (k2 * m4) := by
      exact mul_le_mul_of_nonneg_left hkm_le (by norm_num : (0 : Error) ≤ 2560)
    have hScale' : 2560 * (k : Error) * (params.m : Error) ≤ 2560 * (k2 * m4) := by
      simpa [mul_assoc] using hScale
    calc
      Z2 ≤ 2560 * (k : Error) * (params.m : Error) * E16384 := hZ2
      _ ≤ (2560 * (k2 * m4)) * E16384 := by
        exact mul_le_mul_of_nonneg_right hScale' hE16384NN
      _ = 2560 * k2 * m4 * E16384 := by ring
  have hSum : 6 * Z1 + 6 * Z2 ≤ 150000 * k2 * m4 * E16384 := by
    have hCoeff : (136584 : Error) * k2 * m4 ≤ 150000 * k2 * m4 := by
      have hk2m4NN : 0 ≤ k2 * m4 := by positivity
      nlinarith [hk2m4NN]
    calc
      6 * Z1 + 6 * Z2 ≤ 6 * (20204 * k2 * m4 * E16384) + 6 * (2560 * k2 * m4 * E16384) := by
        nlinarith [hZ1', hZ2']
      _ = (136584 : Error) * k2 * m4 * E16384 := by ring
      _ ≤ (150000 * k2 * m4) * E16384 := by
        exact mul_le_mul_of_nonneg_right hCoeff hE16384NN
      _ = 150000 * k2 * m4 * E16384 := by ring
  simpa [cascadeZeta3, Z1, Z2] using hSum

/-- **Paper lines 214–217 and 230.** The concrete `ζ₃` built from the cascade
chain is rewritten as `ζ₃ ≤ 2 · mainFormalError`. -/
theorem zeta3_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = cascadeZeta2 ζ₁) :
    cascadeZeta3 ζ₁ ζ₂ ≤ 2 * mainFormalError params k eps := by
  rw [hζ₂Eq, hζ₁Eq, hσEq, mainFormalError_eq_envelope]
  have hζ₃ := cascadeZeta3_bound (h := h) (ν := ν) hνNN hν
  have hTightEnvelope :
      stepEnvelope params k eps (16384 : Error) (1280000 : Error) ≤ mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  have hCoeffNN : 0 ≤ 150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  refine hζ₃.trans ?_
  calc
    150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (16384 : Error) (1280000 : Error)
      ≤ 150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_left hTightEnvelope hCoeffNN
    _ = (150000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps := by ring
    _ ≤ (200000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (150000 : Error) ≤ 200000) hk2m4NN) hENN
    _ = 2 *
          (100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
            mainFormalEnvelope params k eps) := by ring

private theorem cascadeZeta4_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeZeta4 (cascadeSigma params k ν)
        (cascadeZeta1 params eps (cascadeSigma params k ν))
        (cascadeZeta3
          (cascadeZeta1 params eps (cascadeSigma params k ν))
          (cascadeZeta2 (cascadeZeta1 params eps (cascadeSigma params k ν)))) ≤
      40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (32768 : Error) (2560000 : Error) := by
  set σ : Error := cascadeSigma params k ν
  set Z1 : Error := cascadeZeta1 params eps σ
  set Z2 : Error := cascadeZeta2 Z1
  set Z3 : Error := cascadeZeta3 Z1 Z2
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  set m2 : Error := (params.m : Error) ^ (2 : ℕ)
  set m4 : Error := (params.m : Error) ^ (4 : ℕ)
  set E1024 : Error := stepEnvelope params k eps (1024 : Error) (80000 : Error)
  set E2048 : Error := stepEnvelope params k eps (2048 : Error) (160000 : Error)
  set E4096 : Error := stepEnvelope params k eps (4096 : Error) (320000 : Error)
  set E16384 : Error := stepEnvelope params k eps (16384 : Error) (1280000 : Error)
  set E32768 : Error := stepEnvelope params k eps (32768 : Error) (2560000 : Error)
  have hE2048NN : 0 ≤ E2048 := by
    simpa [E2048] using stepEnvelope_nonneg (h := h) (n := (2048 : Error)) (N := (160000 : Error))
  have hE4096NN : 0 ≤ E4096 := by
    simpa [E4096] using stepEnvelope_nonneg (h := h) (n := (4096 : Error)) (N := (320000 : Error))
  have hE16384NN : 0 ≤ E16384 := by
    simpa [E16384] using stepEnvelope_nonneg (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
  have hE32768NN : 0 ≤ E32768 := by
    simpa [E32768] using stepEnvelope_nonneg (h := h) (n := (32768 : Error)) (N := (2560000 : Error))
  have hσ : σ ≤ 10000 * k2 * m4 * E1024 := by
    simpa [σ, k2, m4, E1024] using cascadeSigma_tight_bound (h := h) (ν := ν) hν
  have hσ' : σ ≤ 10000 * k2 * m4 * E32768 := by
    calc
      σ ≤ 10000 * k2 * m4 * E1024 := hσ
      _ ≤ 10000 * k2 * m4 * E32768 := by
        have hMono : E1024 ≤ E32768 := by
          simpa [E1024, E32768] using stepEnvelope_le_stepEnvelope (h := h)
            (n₁ := (1024 : Error)) (n₂ := (32768 : Error)) (N₁ := (80000 : Error))
            (N₂ := (2560000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
            (hN₁Pos := by norm_num) (hN := by norm_num)
        exact mul_le_mul_of_nonneg_left hMono (by positivity)
  have hZ1_raw := cascadeZeta1_bound (h := h) (ν := ν) hν
  have hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048 := by
    simpa [σ, Z1, k2, m4, E2048] using hZ1_raw
  have hZ3_raw := cascadeZeta3_bound (h := h) (ν := ν) hνNN hν
  have hZ3 : Z3 ≤ 150000 * k2 * m4 * E16384 := by
    simpa [σ, Z1, Z2, Z3, k2, m4, E16384] using hZ3_raw
  have hZ1NN : 0 ≤ Z1 := by
    simpa [σ, Z1] using cascadeZeta1_nonneg (h := h) (ν := ν) hνNN
  have hZ2NN : 0 ≤ Z2 := by
    unfold Z2 cascadeZeta2
    refine add_nonneg ?_ ?_
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hZ1NN _)
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hZ1NN _)
  have hZ3NN : 0 ≤ Z3 := by
    unfold Z3 cascadeZeta3
    exact add_nonneg (mul_nonneg (by norm_num) hZ1NN) (mul_nonneg (by norm_num) hZ2NN)
  have hX1NN : 0 ≤ 20204 * k2 * m4 * E2048 := by
    positivity [hE2048NN]
  have hsqrtZ1 : Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : Error) * m2 * E4096 := by
    calc
      Real.sqrt (20204 * k2 * m4 * E2048)
        ≤ Real.sqrt (20204 : Error) * (k : Error) * m2 * E4096 := by
          simpa [k2, m2, m4, E2048, E4096,
            show (2 : Error) * 2048 = 4096 by norm_num,
            show (2 : Error) * 160000 = 320000 by norm_num] using
            sqrt_scaled_stepEnvelope_le (h := h)
              (x := 20204 * k2 * m4 * E2048) (C := (20204 : Error))
              (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
      _ ≤ 143 * (k : Error) * m2 * E4096 := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right sqrt20204_le_143
              (show 0 ≤ (k : Error) * m2 * E4096 by positivity [hE4096NN])
  have hE4096 : E4096 ≤ E32768 := by
    simpa [E4096, E32768] using stepEnvelope_le_stepEnvelope (h := h)
      (n₁ := (4096 : Error)) (n₂ := (32768 : Error)) (N₁ := (320000 : Error))
      (N₂ := (2560000 : Error)) (hn₁Pos := by norm_num) (hn := by norm_num)
      (hN₁Pos := by norm_num) (hN := by norm_num)
  have hsqrtZ1' : Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : Error) * m2 * E32768 := by
    calc
      Real.sqrt (20204 * k2 * m4 * E2048) ≤ 143 * (k : Error) * m2 * E4096 := hsqrtZ1
      _ ≤ 143 * (k : Error) * m2 * E32768 :=
        mul_le_mul_of_nonneg_left hE4096 (by positivity)
  have hX3NN : 0 ≤ 150000 * k2 * m4 * E16384 := by
    positivity [hE16384NN]
  have hsqrtZ3 : Real.sqrt (150000 * k2 * m4 * E16384) ≤ 388 * (k : Error) * m2 * E32768 := by
    calc
      Real.sqrt (150000 * k2 * m4 * E16384)
        ≤ Real.sqrt (150000 : Error) * (k : Error) * m2 * E32768 := by
          simpa [k2, m2, m4, E16384, E32768,
            show (2 : Error) * 16384 = 32768 by norm_num,
            show (2 : Error) * 1280000 = 2560000 by norm_num] using
            sqrt_scaled_stepEnvelope_le (h := h)
              (x := 150000 * k2 * m4 * E16384) (C := (150000 : Error))
              (hC := by norm_num) (hx := le_rfl) (hn := by norm_num) (hN := by norm_num)
      _ ≤ 388 * (k : Error) * m2 * E32768 := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_right sqrt150000_le_388
              (show 0 ≤ (k : Error) * m2 * E32768 by positivity [hE32768NN])
  have hsqrtTerm : 2 * Real.sqrt (Z1 + Z3 / 2) ≤ 1062 * k2 * m4 * E32768 := by
    have hZ3half : Z3 / 2 ≤ 150000 * k2 * m4 * E16384 := by
      nlinarith [hZ3, hZ3NN]
    have hinside : Z1 + Z3 / 2 ≤ 20204 * k2 * m4 * E2048 + 150000 * k2 * m4 * E16384 := by
      linarith [hZ1, hZ3half]
    have hsqrtSplit : Real.sqrt (Z1 + Z3 / 2) ≤
        Real.sqrt (20204 * k2 * m4 * E2048) + Real.sqrt (150000 * k2 * m4 * E16384) := by
      calc
        Real.sqrt (Z1 + Z3 / 2)
          ≤ Real.sqrt (20204 * k2 * m4 * E2048 + 150000 * k2 * m4 * E16384) :=
            Real.sqrt_le_sqrt hinside
        _ ≤ Real.sqrt (20204 * k2 * m4 * E2048) + Real.sqrt (150000 * k2 * m4 * E16384) :=
            sqrt_add_le_add_sqrt (by positivity [hE2048NN]) (by positivity [hE16384NN])
    have hkm2 : (k : Error) * m2 ≤ k2 * m4 := by simpa [k2, m2, m4] using h.km2_le_k2m4
    have hkm2z1 : 143 * (k : Error) * m2 * E32768 ≤ 143 * k2 * m4 * E32768 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hkm2 (show 0 ≤ 143 * E32768 by positivity [hE32768NN])
    have hkm2z3 : 388 * (k : Error) * m2 * E32768 ≤ 388 * k2 * m4 * E32768 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hkm2 (show 0 ≤ 388 * E32768 by positivity [hE32768NN])
    nlinarith [hsqrtSplit, hsqrtZ1', hsqrtZ3, hkm2z1, hkm2z3]
  unfold cascadeZeta4
  calc
    2 * σ + 2 * Real.sqrt (Z1 + Z3 / 2)
      ≤ 20000 * k2 * m4 * E32768 + 1062 * k2 * m4 * E32768 := by
        nlinarith [hσ', hsqrtTerm]
    _ ≤ 40000 * k2 * m4 * E32768 := by
        nlinarith [show 0 ≤ k2 * m4 * E32768 by positivity]

/-- **Paper lines 220–228.** The concrete `ζ₄` built from the cascade chain is
absorbed by `mainFormalError`. -/
theorem zeta4_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ ζ₃ : Error} (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = cascadeZeta3 ζ₁ ζ₂) :
    cascadeZeta4 σ ζ₁ ζ₃ ≤ mainFormalError params k eps := by
  rw [hζ₃Eq, hζ₂Eq, hζ₁Eq, hσEq, mainFormalError_eq_envelope]
  have hζ₄ := cascadeZeta4_bound (h := h) (ν := ν) hνNN hν
  have hTightEnvelope :
      stepEnvelope params k eps (32768 : Error) (2560000 : Error) ≤ mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (32768 : Error)) (N := (2560000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  have hCoeffNN : 0 ≤ 40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  refine hζ₄.trans ?_
  calc
    40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        stepEnvelope params k eps (32768 : Error) (2560000 : Error)
      ≤ 40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_left hTightEnvelope hCoeffNN
    _ = (40000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps := by ring
    _ ≤ (100000 * (((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)))) *
          mainFormalEnvelope params k eps :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (40000 : Error) ≤ 100000) hk2m4NN) hENN
    _ = 100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
          mainFormalEnvelope params k eps := by ring

/-- **Paper lines 230–234.** Packages the five cascade bounds into the tuple
used by `mainFormal`. -/
theorem errorCascade_le_mainFormalError {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ ζ₃ : Error}
    (hνNN : 0 ≤ ν)
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = cascadeZeta3 ζ₁ ζ₂) :
    σ ≤ mainFormalError params k eps ∧
    ζ₁ ≤ mainFormalError params k eps ∧
    ζ₂ ≤ mainFormalError params k eps ∧
    ζ₃ ≤ 2 * mainFormalError params k eps ∧
    cascadeZeta4 σ ζ₁ ζ₃ ≤ mainFormalError params k eps := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hσEq, mainFormalError_eq_envelope]
    have hENN := h.envelope_nonneg
    have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
      positivity
    nlinarith [sigma_bound h hν, hENN, hk2m4NN]
  · rw [hζ₁Eq]
    exact zeta1_bound h hν hσEq
  · rw [hζ₂Eq]
    exact zeta2_bound h hνNN hν hσEq hζ₁Eq
  · rw [hζ₃Eq]
    exact zeta3_bound h hνNN hν hσEq hζ₁Eq hζ₂Eq
  · exact zeta4_bound h hνNN hν hσEq hζ₁Eq hζ₂Eq hζ₃Eq

end Test

end MIPStarRE.LDT
