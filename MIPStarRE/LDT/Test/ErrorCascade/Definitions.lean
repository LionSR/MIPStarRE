import Mathlib.Analysis.Complex.ExponentialBounds
import MIPStarRE.LDT.Basic.SqrtBounds

/-!
# Error cascade — core definitions

This module defines the central error quantities `mainFormalError`,
`mainFormalEnvelope`, the cascade variables `σ`, `ζ₁`, `ζ₂`, `ζ₃`, `ζ₄`,
and the `CascadeHypotheses` numeric regime used throughout the error-cascade
bookkeeping for Step 8 of `mainFormal`.

## References

* `references/ldt-paper/inductive_step.tex`, lines 187–234.
-/

open scoped BigOperators

namespace MIPStarRE.LDT

namespace Test

/-- The formal final error envelope for `thm:main-formal`.

The sharper pre-completion line-169 repair keeps the point-transport scale at
the original `1/40000` exponent used by the surrounding Step 8 cascade. -/
noncomputable def mainFormalError (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
    (Real.rpow eps (1 / (40000 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (40000 : Error)) +
      Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))))

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

/-- Formal Step 6 quantity
`ζ₂ = 200·ζ₁^(1/4) + 42·ζ₁^(1/8)`.

The paper prints coefficient `40` in `inductive_step.tex:149`; the extra `2`
absorbs the residual `+ 2ζ₁` term from completing an orthonormalized
submeasurement when `0 ≤ ζ₁ ≤ 1`. -/
noncomputable def cascadeZeta2 (ζ₁ : Error) : Error :=
  200 * Real.rpow ζ₁ (1 / (4 : Error)) + 42 * Real.rpow ζ₁ (1 / (8 : Error))

/-- Paper quantity `ζ₃ = 6·ζ₁ + 6·ζ₂` (see `inductive_step.tex:158`). -/
noncomputable def cascadeZeta3 (ζ₁ ζ₂ : Error) : Error :=
  6 * ζ₁ + 6 * ζ₂

/-- Paper quantity `ζ₄ = 2σ + 2·√(ζ₁ + ζ₃/2)` (see `inductive_step.tex:181`). -/
noncomputable def cascadeZeta4 (σ ζ₁ ζ₃ : Error) : Error :=
  2 * σ + 2 * Real.sqrt (ζ₁ + ζ₃ / 2)

/-- Repaired line-169 error obtained by the checked local pre-completion route.

Paper line 169 is printed with the exact error `ζ₁`; the checked local repair
instead yields `ζ₁ + 10·ζ₁^(1/8)`.  The additional term comes from
`sqrt (orthonormalizationError ζ₁) = sqrt (100·ζ₁^(1/4)) = 10·ζ₁^(1/8)` in
`ProjectivizationLine169Repair.leftConsistency_with_orthonormalization_loss`
and its Bob-side mirror.

This is an internal repaired-route scalar for the Step 6 transport.  It is not
the paper's printed line-169 parameter, and it is later absorbed into
`mainFormalError`. -/
noncomputable def cascadeLine169RepairError (ζ₁ : Error) : Error :=
  ζ₁ + 10 * Real.rpow ζ₁ (1 / (8 : Error))

/-- Repaired final point-consistency scalar obtained by substituting the checked
line-169 repair error into the last Step 8 transport triangle.

The paper's `ζ₄` at `references/ldt-paper/inductive_step.tex:181` is
`2σ + 2·√(ζ₁ + ζ₃/2)`.  This repaired variant replaces `ζ₁` by the internal
checked line-169 repair error above, so it is likewise an internal scalar that
is subsequently absorbed into `mainFormalError` rather than a new paper-facing
theorem parameter. -/
noncomputable def cascadeZeta4Repaired (σ ζ₁ ζ₃ : Error) : Error :=
  2 * σ + 2 * Real.sqrt (cascadeLine169RepairError ζ₁ + ζ₃ / 2)

/-- Paper origin: `references/ldt-paper/inductive_step.tex:130-211`
(`\label{eq:G-self-consistency}` through `\label{eq:another-goal}`, error cascade
ζ₁–ζ₄); blueprint `\label{def:main-formal-error-cascade}`.

Standing numeric regime used throughout the cascade bounds: parameters
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

end Test

end MIPStarRE.LDT
