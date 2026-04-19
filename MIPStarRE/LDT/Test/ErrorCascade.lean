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
* The **cascade bound** (`sigma_bound`, `zeta1_bound`, …), taking the
  paper's upstream bound at its native exponent as a hypothesis and
  concluding that the current step's variable is absorbed by the final
  envelope.

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

/-- `k² · m⁴ ≥ 1`. -/
theorem k2_m4_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) *
    ((params.m : Error) ^ (4 : ℕ)) := by
  nlinarith [h.k2_ge_one, h.m4_ge_one]

end CascadeHypotheses

/-- For `x ∈ [0,1]` and `0 < n ≤ 40000`, `x^(1/n) ≤ x^(1/40000)`.

For `x ≤ 1`, a larger exponent gives a smaller value, so the paper's finer
exponent `1/n` (with `n ≤ 40000`, e.g. `1/1024`) lies below the coarser
envelope exponent `1/40000`. -/
private theorem rpow_le_envelope_exponent {x : Error} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {n : Error} (hnPos : 0 < n) (hn : n ≤ 40000) :
    Real.rpow x (1 / n) ≤ Real.rpow x (1 / (40000 : Error)) := by
  have hinvNN : (0 : Error) ≤ 1 / (40000 : Error) := by positivity
  have hle : 1 / (40000 : Error) ≤ 1 / n := one_div_le_one_div_of_le hnPos hn
  exact Real.rpow_le_rpow_of_exponent_ge' hx hx1 hinvNN hle

/-- For `k ≥ 0, m > 0, N₁ ≤ N₂`, `exp(-k/(N₁ m²)) ≤ exp(-k/(N₂ m²))`.

The envelope decay constant `2560000 m²` dominates each finer paper constant. -/
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

/-- A paper-local envelope with exponent `1/n` and decay scale `N` is absorbed
by `mainFormalEnvelope` whenever `n ≤ 40000` and `N ≤ 2560000`. -/
private theorem stepEnvelope_le_mainFormalEnvelope {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {n N : Error}
    (hnPos : 0 < n) (hn : n ≤ 40000) (hNPos : 0 < N) (hN : N ≤ 2560000) :
    Real.rpow eps (1 / n) +
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / n) +
      Real.exp (-((k : Error) / (N * ((params.m : Error) ^ (2 : ℕ))))) ≤
        mainFormalEnvelope params k eps := by
  unfold mainFormalEnvelope
  have hEps := rpow_le_envelope_exponent h.hepsNN h.hepsOne hnPos hn
  have hDq := rpow_le_envelope_exponent h.dqNN h.dqLeOne hnPos hn
  have hmPos : 0 < (params.m : Error) := by linarith [h.hm]
  have hExp := exp_neg_le_of_denom_ge k (params.m : Error) hmPos hNPos hN
  linarith

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
  unfold cascadeSigma
  set m2 : Error := (params.m : Error) ^ (2 : ℕ) with hm2_def
  set m4 : Error := (params.m : Error) ^ (4 : ℕ) with hm4_def
  set k2 : Error := (k : Error) ^ (2 : ℕ)
  have hm2NN : 0 ≤ m2 := by positivity
  have hm4NN : 0 ≤ m4 := by positivity
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
                Real.rpow ((params.d : Error) / (params.q : Error))
                  (1 / (1024 : Error)))) :=
            mul_le_mul_of_nonneg_left hν hm2NN
      _ = 10000 * k2 * (m2 * m2) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error))
                (1 / (1024 : Error))) := hreorder
      _ = 10000 * k2 * m4 *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error))
                (1 / (1024 : Error))) := by rw [hm2_sq_m4]
  have hmPos : 0 < (params.m : Error) := by linarith [h.hm]
  have hExpMono :
      Real.exp (-((k : Error) / (80000 * m2))) ≤
        Real.exp (-((k : Error) / (2560000 * m2))) := by
    have := exp_neg_le_of_denom_ge k (params.m : Error) hmPos
      (by norm_num : (0 : Error) < 80000) (by norm_num : (80000 : Error) ≤ 2560000)
    simpa [hm2_def] using this
  have hScaleGeOne : (1 : Error) ≤ 10000 * k2 := by
    nlinarith [hk2_ge_one]
  have hm2_le_10k2m4 : m2 ≤ 10000 * k2 * m4 := by
    calc
      m2 ≤ m4 := hm2_le_m4
      _ ≤ (10000 * k2) * m4 := by
        nlinarith [hScaleGeOne, hm4NN]
      _ = 10000 * k2 * m4 := by ring
  have hStep2 :
      m2 * Real.exp (-((k : Error) / (80000 * m2))) ≤
        10000 * k2 * m4 * Real.exp (-((k : Error) / (2560000 * m2))) := by
    have hExpNN : 0 ≤ Real.exp (-((k : Error) / (2560000 * m2))) := Real.exp_nonneg _
    calc
      m2 * Real.exp (-((k : Error) / (80000 * m2)))
          ≤ m2 * Real.exp (-((k : Error) / (2560000 * m2))) :=
            mul_le_mul_of_nonneg_left hExpMono hm2NN
      _ ≤ 10000 * k2 * m4 * Real.exp (-((k : Error) / (2560000 * m2))) :=
            mul_le_mul_of_nonneg_right hm2_le_10k2m4 hExpNN
  have hStepEnvelope :
      Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) +
        Real.exp (-((k : Error) / (2560000 * m2))) ≤
          mainFormalEnvelope params k eps := by
    have := stepEnvelope_le_mainFormalEnvelope (h := h) (n := (1024 : Error))
      (N := (2560000 : Error)) (hnPos := by norm_num) (hn := by norm_num)
      (hNPos := by norm_num) (hN := by norm_num)
    simpa [hm2_def] using this
  have hCoeffNN : 0 ≤ 10000 * k2 * m4 := by positivity
  have hExpand : m2 * (ν + Real.exp (-((k : Error) / (80000 * m2)))) =
      m2 * ν + m2 * Real.exp (-((k : Error) / (80000 * m2))) := by ring
  rw [hExpand]
  calc
    m2 * ν + m2 * Real.exp (-((k : Error) / (80000 * m2)))
        ≤ 10000 * k2 * m4 *
              (Real.rpow eps (1 / (1024 : Error)) +
                Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) +
            10000 * k2 * m4 * Real.exp (-((k : Error) / (2560000 * m2))) := by
          linarith [hStep1, hStep2]
    _ = 10000 * k2 * m4 *
          (Real.rpow eps (1 / (1024 : Error)) +
            Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) +
            Real.exp (-((k : Error) / (2560000 * m2)))) := by ring
    _ ≤ 10000 * k2 * m4 * mainFormalEnvelope params k eps :=
          mul_le_mul_of_nonneg_left hStepEnvelope hCoeffNN

/-- **Paper lines 196–201.** The paper's bound for `ζ₁` is absorbed by
`mainFormalError`. -/
theorem zeta1_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {σ : Error}
    (hζ₁ : cascadeZeta1 params eps σ ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        (Real.rpow eps (1 / (2048 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) +
          Real.exp (-((k : Error) / (160000 * ((params.m : Error) ^ (2 : ℕ))))))) :
    cascadeZeta1 params eps σ ≤ mainFormalError params k eps := by
  rw [mainFormalError_eq_envelope]
  have hTightEnvelope :
      Real.rpow eps (1 / (2048 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) +
        Real.exp (-((k : Error) / (160000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
          mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (2048 : Error)) (N := (160000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  have hCoeffNN : 0 ≤ 20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  refine hζ₁.trans ?_
  calc
    20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        (Real.rpow eps (1 / (2048 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) +
          Real.exp (-((k : Error) / (160000 * ((params.m : Error) ^ (2 : ℕ))))))
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

/-- **Paper lines 205–212.** The paper's bound for `ζ₂` is absorbed by
`mainFormalError`. -/
theorem zeta2_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ζ₁ : Error}
    (hζ₂ : cascadeZeta2 ζ₁ ≤
      2560 * (k : Error) * (params.m : Error) *
        (Real.rpow eps (1 / (16384 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (16384 : Error)) +
          Real.exp (-((k : Error) / (1280000 * ((params.m : Error) ^ (2 : ℕ))))))) :
    cascadeZeta2 ζ₁ ≤ mainFormalError params k eps := by
  rw [mainFormalError_eq_envelope]
  have hTightEnvelope :
      Real.rpow eps (1 / (16384 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (16384 : Error)) +
        Real.exp (-((k : Error) / (1280000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
          mainFormalEnvelope params k eps :=
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
        (Real.rpow eps (1 / (16384 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (16384 : Error)) +
          Real.exp (-((k : Error) / (1280000 * ((params.m : Error) ^ (2 : ℕ))))))
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

/-- **Paper lines 214–217 and 230.** The paper's bound for `ζ₃` is rewritten as
`ζ₃ ≤ 2 · mainFormalError`. -/
theorem zeta3_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ζ₁ ζ₂ : Error}
    (hζ₃ : cascadeZeta3 ζ₁ ζ₂ ≤
      150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        (Real.rpow eps (1 / (16384 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (16384 : Error)) +
          Real.exp (-((k : Error) / (1280000 * ((params.m : Error) ^ (2 : ℕ))))))) :
    cascadeZeta3 ζ₁ ζ₂ ≤ 2 * mainFormalError params k eps := by
  rw [mainFormalError_eq_envelope]
  have hTightEnvelope :
      Real.rpow eps (1 / (16384 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (16384 : Error)) +
        Real.exp (-((k : Error) / (1280000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
          mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (16384 : Error)) (N := (1280000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  have hCoeffNN : 0 ≤ 150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  refine hζ₃.trans ?_
  calc
    150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        (Real.rpow eps (1 / (16384 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (16384 : Error)) +
          Real.exp (-((k : Error) / (1280000 * ((params.m : Error) ^ (2 : ℕ))))))
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

/-- **Paper lines 220–228.** The paper's bound for `ζ₄` is absorbed by
`mainFormalError`. -/
theorem zeta4_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {σ ζ₁ ζ₃ : Error}
    (hζ₄ : cascadeZeta4 σ ζ₁ ζ₃ ≤
      40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        (Real.rpow eps (1 / (32768 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32768 : Error)) +
          Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))))) :
    cascadeZeta4 σ ζ₁ ζ₃ ≤ mainFormalError params k eps := by
  rw [mainFormalError_eq_envelope]
  have hTightEnvelope :
      Real.rpow eps (1 / (32768 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32768 : Error)) +
        Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))) ≤
          mainFormalEnvelope params k eps :=
    stepEnvelope_le_mainFormalEnvelope (h := h) (n := (32768 : Error)) (N := (2560000 : Error))
      (hnPos := by norm_num) (hn := by norm_num) (hNPos := by norm_num) (hN := by norm_num)
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  have hCoeffNN : 0 ≤ 40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  refine hζ₄.trans ?_
  calc
    40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        (Real.rpow eps (1 / (32768 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32768 : Error)) +
          Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))))
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
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = cascadeZeta3 ζ₁ ζ₂)
    (hζ₁Bound : cascadeZeta1 params eps σ ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        (Real.rpow eps (1 / (2048 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2048 : Error)) +
          Real.exp (-((k : Error) / (160000 * ((params.m : Error) ^ (2 : ℕ)))))))
    (hζ₂Bound : cascadeZeta2 ζ₁ ≤
      2560 * (k : Error) * (params.m : Error) *
        (Real.rpow eps (1 / (16384 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (16384 : Error)) +
          Real.exp (-((k : Error) / (1280000 * ((params.m : Error) ^ (2 : ℕ)))))))
    (hζ₃Bound : cascadeZeta3 ζ₁ ζ₂ ≤
      150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        (Real.rpow eps (1 / (16384 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (16384 : Error)) +
          Real.exp (-((k : Error) / (1280000 * ((params.m : Error) ^ (2 : ℕ)))))))
    (hζ₄Bound : cascadeZeta4 σ ζ₁ ζ₃ ≤
      40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        (Real.rpow eps (1 / (32768 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (32768 : Error)) +
          Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))))) :
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
    exact zeta1_bound h hζ₁Bound
  · rw [hζ₂Eq]
    exact zeta2_bound h hζ₂Bound
  · rw [hζ₃Eq]
    exact zeta3_bound h hζ₃Bound
  · exact zeta4_bound h hζ₄Bound

end Test

end MIPStarRE.LDT
