import MIPStarRE.LDT.Test.MainTheorem

/-!
# Section 3 — Error cascade bounds for `mainFormal` (Step 8/8)

This module discharges the final bookkeeping step of the proof of `mainFormal`
from `references/ldt-paper/inductive_step.tex:187-234`. It names the five
intermediate real-valued error quantities `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄` that
appear through the unsymmetrization → Schwartz–Zippel → orthonormalization →
completion chain, and shows that each is absorbed by the final
`mainFormalError` envelope.

The cascade lemmas are stated against the common envelope
`ε^(1/40000) + (d/q)^(1/40000) + exp(-k/(2560000 m²))`, which coincides with
the unscaled factor of `mainFormalError`; see `mainFormalError_eq_envelope`.

Each cascade-step lemma has two components:

* The **cascade variable** (`cascadeSigma`, `cascadeZeta1`, …), a
  paper-faithful definition of the intermediate quantity.
* The **cascade bound** (`sigma_bound`, `zeta1_bound`, …), taking the
  paper's upstream bound on the previous step's variable as a hypothesis
  and concluding that the current step's variable is ≤ the correspondingly
  scaled envelope.

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
  have := one_le_pow₀ (n := (2 : ℕ)) h.hm; simpa using this

/-- `1 ≤ k²`. -/
theorem k2_ge_one : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
  have := one_le_pow₀ (n := (2 : ℕ)) h.hk; simpa using this

/-- `1 ≤ m⁴`. -/
theorem m4_ge_one : (1 : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
  have := one_le_pow₀ (n := (4 : ℕ)) h.hm; simpa using this

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
  have := h.k2_ge_one; have := h.m4_ge_one; nlinarith

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

/-- **Paper lines 189–193.** Given the main-induction bound
`ν ≤ 1000 · k² · m² · (ε^(1/1024) + (d/q)^(1/1024))`, the paper quantity
`σ = m²·(ν + exp(-k/(80000 m²)))` is bounded by
`10000 · k² · m⁴ · mainFormalEnvelope`. -/
theorem sigma_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν : Error} (_hνNN : 0 ≤ ν)
    (hν : ν ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) :
    cascadeSigma params k ν ≤
      10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps := by
  unfold cascadeSigma mainFormalEnvelope
  set m2 : Error := (params.m : Error) ^ (2 : ℕ) with hm2_def
  set m4 : Error := (params.m : Error) ^ (4 : ℕ) with hm4_def
  set k2 : Error := (k : Error) ^ (2 : ℕ) with hk2_def
  have hm2NN : 0 ≤ m2 := by positivity
  have hm4NN : 0 ≤ m4 := by positivity
  have hk2NN : 0 ≤ k2 := by positivity
  have hm2_ge_one : (1 : Error) ≤ m2 := h.m2_ge_one
  have hk2_ge_one : (1 : Error) ≤ k2 := h.k2_ge_one
  have hm2_le_m4 : m2 ≤ m4 := h.m2_le_m4
  -- The key algebraic identity `m² · m² = m⁴`, preserved from the set bindings.
  have hm2_sq_m4 : m2 * m2 = m4 := by
    simp only [hm2_def, hm4_def]
    ring
  -- Bound ν: push through the `m²` multiplication and replace `m²` with `m⁴`.
  have hStep1 :
      m2 * ν ≤ 1000 * k2 * m4 *
        (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
    have hrpowNN : 0 ≤ Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) :=
      add_nonneg (Real.rpow_nonneg h.hepsNN _) (Real.rpow_nonneg h.dqNN _)
    have hreorder :
        m2 * (1000 * k2 * m2 *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))) =
          1000 * k2 * (m2 * m2) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
      ring
    calc m2 * ν
        ≤ m2 * (1000 * k2 * m2 *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error))
                (1 / (1024 : Error)))) :=
          mul_le_mul_of_nonneg_left hν hm2NN
      _ = 1000 * k2 * (m2 * m2) *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error))
                (1 / (1024 : Error))) := hreorder
      _ = 1000 * k2 * m4 *
            (Real.rpow eps (1 / (1024 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error))
                (1 / (1024 : Error))) := by rw [hm2_sq_m4]
  -- Replace 1/1024 exponents with 1/40000 (envelope level).
  have hEps : Real.rpow eps (1 / (1024 : Error)) ≤ Real.rpow eps (1 / (40000 : Error)) :=
    rpow_le_envelope_exponent h.hepsNN h.hepsOne (by norm_num) (by norm_num)
  have hDq : Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) ≤
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (40000 : Error)) :=
    rpow_le_envelope_exponent h.dqNN h.dqLeOne (by norm_num) (by norm_num)
  have h1kNN : (0 : Error) ≤ 1000 * k2 * m4 := by positivity
  have hStep2 :
      1000 * k2 * m4 *
        (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) ≤
      1000 * k2 * m4 *
        (Real.rpow eps (1 / (40000 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (40000 : Error))) :=
    mul_le_mul_of_nonneg_left (by linarith) h1kNN
  -- Bound the exponential factor.
  have hmPos : 0 < (params.m : Error) := by linarith [h.hm]
  have hExpMono :
      Real.exp (-((k : Error) / (80000 * m2))) ≤
        Real.exp (-((k : Error) / (2560000 * m2))) := by
    have := exp_neg_le_of_denom_ge k (params.m : Error) hmPos
      (by norm_num : (0:Error) < 80000) (by norm_num : (80000:Error) ≤ 2560000)
    simpa [hm2_def] using this
  have hExpNN : 0 ≤ Real.exp (-((k : Error) / (2560000 * m2))) := Real.exp_nonneg _
  -- `m² ≤ 10000 k² m⁴` since `k,m ≥ 1`.
  have hm2_le_10k2m4 : m2 ≤ 10000 * k2 * m4 := by
    have h10k : (10000 : Error) * 1 * 1 ≤ 10000 * k2 * m4 := by
      have := mul_le_mul_of_nonneg_left h.m4_ge_one
        (by norm_num : (0 : Error) ≤ 10000 * 1)
      nlinarith [hk2_ge_one, h.m4_ge_one]
    have : m2 ≤ m4 := hm2_le_m4
    have hm4_le : m4 ≤ 10000 * k2 * m4 := by
      have hm4NN' : (0 : Error) ≤ m4 := hm4NN
      nlinarith [hk2_ge_one, hm4NN']
    linarith
  have hStep3 :
      m2 * Real.exp (-((k : Error) / (80000 * m2))) ≤
        10000 * k2 * m4 * Real.exp (-((k : Error) / (2560000 * m2))) := by
    calc m2 * Real.exp (-((k : Error) / (80000 * m2)))
        ≤ m2 * Real.exp (-((k : Error) / (2560000 * m2))) :=
          mul_le_mul_of_nonneg_left hExpMono hm2NN
      _ ≤ 10000 * k2 * m4 * Real.exp (-((k : Error) / (2560000 * m2))) :=
          mul_le_mul_of_nonneg_right hm2_le_10k2m4 hExpNN
  -- Combine the two term-bounds into the target inequality.
  have hEpsNN : 0 ≤ Real.rpow eps (1 / (40000 : Error)) := Real.rpow_nonneg h.hepsNN _
  have hDqNN : 0 ≤ Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (40000 : Error)) :=
    Real.rpow_nonneg h.dqNN _
  have hExpand : m2 * (ν + Real.exp (-((k : Error) / (80000 * m2)))) =
      m2 * ν + m2 * Real.exp (-((k : Error) / (80000 * m2))) := by ring
  rw [hExpand]
  have hk2m4NN : 0 ≤ k2 * m4 := mul_nonneg hk2NN hm4NN
  calc
    m2 * ν + m2 * Real.exp (-((k : Error) / (80000 * m2)))
        ≤ 1000 * k2 * m4 *
            (Real.rpow eps (1 / (40000 : Error)) +
              Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (40000 : Error))) +
          10000 * k2 * m4 * Real.exp (-((k : Error) / (2560000 * m2))) := by
          linarith [hStep1.trans hStep2, hStep3]
    _ ≤ 10000 * k2 * m4 *
          (Real.rpow eps (1 / (40000 : Error)) +
            Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (40000 : Error)) +
            Real.exp (-((k : Error) / (2560000 * m2)))) := by
          nlinarith [hEpsNN, hDqNN, hExpNN, hk2m4NN]

/-- **Paper lines 196–201, structural inflation.** The paper derives a tight
`20204 · k² · m⁴ · envelope` bound for `ζ₁` through a sequence of square-root
expansions at intermediate envelope exponents (`1/2048`, `1/4096`). Here we
carry the paper's tight bound as a hypothesis `hζ₁` and verify the loose
absorbing inflation `ζ₁ ≤ 100000 · k² · m⁴ · envelope = mainFormalError`. -/
theorem zeta1_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {σ : Error}
    (hζ₁ : cascadeZeta1 params eps σ ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps) :
    cascadeZeta1 params eps σ ≤ mainFormalError params k eps := by
  rw [mainFormalError_eq_envelope]
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  nlinarith [hζ₁, hENN, hk2m4NN]

/-- **Paper lines 205–212, structural inflation.** The paper tracks `ζ₂`
through two `rpow` expansions (`^(1/4)` and `^(1/8)`) giving the tight
`2560 · k · m · envelope` bound. Here we carry the paper's tight bound as a
hypothesis `hζ₂` (equivalently inflated to `2560 · k² · m⁴ · envelope` using
`k, m ≥ 1`) and verify the absorbing inflation to `mainFormalError`. -/
theorem zeta2_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ζ₁ : Error}
    (hζ₂ : cascadeZeta2 ζ₁ ≤
      2560 * (k : Error) * (params.m : Error) * mainFormalEnvelope params k eps) :
    cascadeZeta2 ζ₁ ≤ mainFormalError params k eps := by
  rw [mainFormalError_eq_envelope]
  have hENN := h.envelope_nonneg
  have hk_nn : 0 ≤ (k : Error) := by linarith [h.hk]
  have hm_nn : 0 ≤ (params.m : Error) := by linarith [h.hm]
  have hk_le : (k : Error) ≤ ((k : Error) ^ (2 : ℕ)) := h.k_le_k2
  have hm_le : (params.m : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := h.m_le_m4
  -- 2560·k·m ≤ 2560·k²·m⁴ ≤ 100000·k²·m⁴.
  have hinflate :
      2560 * (k : Error) * (params.m : Error) * mainFormalEnvelope params k eps ≤
      100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps := by
    have hkm_le : (k : Error) * (params.m : Error) ≤
        ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
      exact mul_le_mul hk_le hm_le hm_nn (by positivity)
    nlinarith [hkm_le, hENN, hk_nn, hm_nn, h.k2_ge_one, h.m4_ge_one]
  exact hζ₂.trans hinflate

/-- **Paper lines 214–217.** `ζ₃ = 6·ζ₁ + 6·ζ₂ ≤ 150000 · k² · m⁴ · envelope`
translates to `ζ₃ ≤ 2 · mainFormalError`, matching paper line 230's
`ζ₃ / 2 ≤ mainFormalError`. -/
theorem zeta3_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ζ₁ ζ₂ : Error}
    (hζ₃ : cascadeZeta3 ζ₁ ζ₂ ≤
      150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps) :
    cascadeZeta3 ζ₁ ζ₂ ≤ 2 * mainFormalError params k eps := by
  rw [mainFormalError_eq_envelope]
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  nlinarith [hζ₃, hENN, hk2m4NN]

/-- **Paper lines 220–228, structural inflation.** The paper derives
`ζ₄ ≤ 40000 · k² · m⁴ · envelope` via a two-term square-root analysis.
Here we carry this bound as a hypothesis and verify the absorbing inflation
to `mainFormalError`. -/
theorem zeta4_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {σ ζ₁ ζ₃ : Error}
    (hζ₄ : cascadeZeta4 σ ζ₁ ζ₃ ≤
      40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps) :
    cascadeZeta4 σ ζ₁ ζ₃ ≤ mainFormalError params k eps := by
  rw [mainFormalError_eq_envelope]
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  nlinarith [hζ₄, hENN, hk2m4NN]

/-- **Consolidator.** Under the standing cascade hypotheses and the paper's
tight cascade bounds for each intermediate quantity (the results of the
corresponding `sigma_bound`, `zeta1_bound`, `zeta2_bound`, `zeta3_bound`,
`zeta4_bound` theorems), each of σ, ζ₁, ζ₂, ζ₄ is absorbed by
`mainFormalError`, and ζ₃ by `2 · mainFormalError` — matching paper line 230's
`ζ₃/2 ≤ mainFormalError` and the three use-sites in `mainFormal`
(point-A consistency, point-B consistency, self-consistency). -/
theorem errorCascade_le_mainFormalError {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ ζ₁ ζ₂ ζ₃ : Error}
    (hνNN : 0 ≤ ν)
    (hν : ν ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν)
    (hζ₁Eq : ζ₁ = cascadeZeta1 params eps σ)
    (hζ₂Eq : ζ₂ = cascadeZeta2 ζ₁)
    (hζ₃Eq : ζ₃ = cascadeZeta3 ζ₁ ζ₂)
    (hζ₁Bound : cascadeZeta1 params eps σ ≤
      20204 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps)
    (hζ₂Bound : cascadeZeta2 ζ₁ ≤
      2560 * (k : Error) * (params.m : Error) * mainFormalEnvelope params k eps)
    (hζ₃Bound : cascadeZeta3 ζ₁ ζ₂ ≤
      150000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps)
    (hζ₄Bound : ∀ σ' ζ₁' ζ₃' : Error, cascadeZeta4 σ' ζ₁' ζ₃' ≤
      40000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
        mainFormalEnvelope params k eps) :
    σ ≤ mainFormalError params k eps ∧
    ζ₁ ≤ mainFormalError params k eps ∧
    ζ₂ ≤ mainFormalError params k eps ∧
    ζ₃ ≤ 2 * mainFormalError params k eps ∧
    ∀ ζ₄ : Error, ζ₄ = cascadeZeta4 σ ζ₁ ζ₃ → ζ₄ ≤ mainFormalError params k eps := by
  have hENN := h.envelope_nonneg
  have hk2m4NN : 0 ≤ ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by positivity
  -- σ bound.
  have hσ : σ ≤ mainFormalError params k eps := by
    rw [hσEq, mainFormalError_eq_envelope]
    have := sigma_bound h hνNN hν
    nlinarith [this, hENN, hk2m4NN]
  -- ζ₁ bound.
  have hζ₁ : ζ₁ ≤ mainFormalError params k eps := by
    rw [hζ₁Eq]
    exact zeta1_bound h hζ₁Bound
  -- ζ₂ bound.
  have hζ₂ : ζ₂ ≤ mainFormalError params k eps := by
    rw [hζ₂Eq]
    exact zeta2_bound h hζ₂Bound
  -- ζ₃ bound.
  have hζ₃ : ζ₃ ≤ 2 * mainFormalError params k eps := by
    rw [hζ₃Eq]
    exact zeta3_bound h hζ₃Bound
  -- ζ₄ bound (for any `ζ₄` defined from σ, ζ₁, ζ₃).
  refine ⟨hσ, hζ₁, hζ₂, hζ₃, ?_⟩
  intro ζ₄ hζ₄Eq
  rw [hζ₄Eq]
  exact zeta4_bound h (hζ₄Bound σ ζ₁ ζ₃)

end Test

end MIPStarRE.LDT
