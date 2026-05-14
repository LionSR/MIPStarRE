import MIPStarRE.LDT.Test.MainTheorem.ClassicalAndBase
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic

/-!
# Main-formal error scalars

Section 3 error cascade for the `mainFormal` assembly.  This module defines
the five scalars that appear in the paper's error calculation:

* `σ` — the symmetrized induction consistency error
* `ζ₁` — the cross-consistency error after unsymmetrization
* `ζ₂` — the orthonormalize-and-complete closeness error
* `ζ₃` — the projective self-consistency error
* `ζ₄` — the final point-consistency error

The core structure `MainFormalCascadeScalars` (Prop) bundles the three
hypotheses needed to invoke the checked Step 8 bound
`errorCascade_le_mainFormalError`:

* `cascadeHypotheses` — the standing scalar regime (`q > 0`, `k ≥ 1`,
  `m ≥ 1`, `0 ≤ ε ≤ 1`, `d ≤ q`).
* `inductionNu_nonneg` — nonnegativity of the symmetrized main-induction
  `ν` at `(3ε, 3ε, 3ε)`.
* `inductionNu_bound` — the paper line 71–73 coarsening
  `ν ≤ 10000 k² m² (ε^{1/1024} + (d/q)^{1/1024})`.

The cascade comparisons `ζ₁ ≤ …`, `ζ₃ ≤ 2·mainFormalError`, etc. are then
derived in the private theorem `cascadeBounds` via
`errorCascade_le_mainFormalError`, which calls the already-formalized
error-cascade estimates from `LDT.Test.ErrorCascade`.  The module also
provides the vacuous-branch analysis (`mainFormalError_ge_one_of_*`) and
the coarsening lemma that absorbs `orthonormalizeAndCompleteError` into
`ζ₂` (`orthonormalizeAndCompleteError_zeta1_le_zeta2`).

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  error computations (lines 68–75, 186–234).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-error-cascade}`,
  `\label{thm:sigma-bound-main-formal}`, and
  `\label{thm:zeta-bounds-main-formal}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- The Section 3 specialization of the main-induction `ν` after Step 1
symmetrization.

Paper lines 68--75 apply `thm:main-induction` to the symmetrized strategy with
errors `(3ε, 3ε, 3ε)` and then coarsen its `ν` to the Section 3 scalar cascade.
This definition keeps the pre-coarsened main-induction quantity available for the
main theorem conclusion. -/
noncomputable def mainFormalInductionNu (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  MainInductionStep.mainInductionNu params k (3 * eps) (3 * eps) (3 * eps)

/-- The `σ` built from `mainFormalInductionNu` is definitionally the Section 6
main-induction error at `(3ε, 3ε, 3ε)`.

This is the exact scalar handoff between paper lines 75--81 and the cascade
notation used from line 133 onward. -/
theorem mainFormalCascadeSigma_eq_mainInductionError (params : Parameters)
    (k : ℕ) (eps : Error) :
    cascadeSigma params k (mainFormalInductionNu params k eps) =
      MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps) :=
  rfl

/-- Nonnegativity of the symmetrized main-induction `ν` under the standing
cascade hypotheses. -/
theorem mainFormalInductionNu_nonneg {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    0 ≤ mainFormalInductionNu params k eps := by
  unfold mainFormalInductionNu MainInductionStep.mainInductionNu
  have hthree_eps_nonneg : 0 ≤ 3 * eps := by nlinarith [h.hepsNN]
  have hthree_term : 0 ≤ Real.rpow (3 * eps) (1 / (1024 : Error)) :=
    Real.rpow_nonneg hthree_eps_nonneg _
  have hdq_term : 0 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
      (1 / (1024 : Error)) :=
    Real.rpow_nonneg h.dqNN _
  have hsum : 0 ≤ Real.rpow (3 * eps) (1 / (1024 : Error)) +
      Real.rpow (3 * eps) (1 / (1024 : Error)) +
      Real.rpow (3 * eps) (1 / (1024 : Error)) +
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) := by
    nlinarith
  have hcoeff : 0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) *
      ((params.m : Error) ^ (2 : ℕ)) := by
    positivity
  exact mul_nonneg hcoeff hsum

/-- Paper lines 71--73: after applying main induction to the symmetrized strategy,
the resulting `ν` at errors `(3ε,3ε,3ε)` is bounded by the coarser Section 3
quantity `10000 k² m² (ε^(1/1024) + (d/q)^(1/1024))`. -/
theorem mainFormalInductionNu_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    mainFormalInductionNu params k eps ≤
      10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
        (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
  unfold mainFormalInductionNu MainInductionStep.mainInductionNu
  set r : Error := 1 / (1024 : Error)
  set e : Error := Real.rpow eps r
  set dq : Error := Real.rpow ((params.d : Error) / (params.q : Error)) r
  have he_nonneg : 0 ≤ e := by
    simpa [e, r] using Real.rpow_nonneg h.hepsNN (1 / (1024 : Error))
  have hdq_nonneg : 0 ≤ dq := by
    simpa [dq, r] using Real.rpow_nonneg h.dqNN (1 / (1024 : Error))
  have hthree_pow_le : Real.rpow (3 * eps) r ≤ 3 * e := by
    calc
      Real.rpow (3 * eps) r = Real.rpow (3 : Error) r * e := by
        simpa [e, r] using
          (Real.mul_rpow (x := (3 : Error)) (y := eps) (z := (1 / (1024 : Error)))
            (by norm_num) h.hepsNN)
      _ ≤ 3 * e := by
        have h3 : Real.rpow (3 : Error) r ≤ 3 := by
          simpa [r, Real.rpow_one] using
            Real.rpow_le_self_of_one_le (x := (3 : Error)) (y := (1 / (1024 : Error)))
              (by norm_num) (by norm_num)
        exact mul_le_mul_of_nonneg_right h3 he_nonneg
  have hsum :
      Real.rpow (3 * eps) r + Real.rpow (3 * eps) r + Real.rpow (3 * eps) r + dq ≤
        10 * (e + dq) := by
    nlinarith [hthree_pow_le, he_nonneg, hdq_nonneg]
  have hcoeff_nonneg :
      0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) := by
    positivity
  calc
    1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
        (Real.rpow (3 * eps) r + Real.rpow (3 * eps) r + Real.rpow (3 * eps) r + dq)
      ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
          (10 * (e + dq)) := by
        exact mul_le_mul_of_nonneg_left hsum hcoeff_nonneg
    _ = 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
          (e + dq) := by ring

/-- If the unscaled Step 8 envelope is already at least `1`, then the public
`mainFormalError` envelope is also at least `1`. -/
theorem mainFormalError_ge_one_of_one_le_envelope
    (params : Parameters) (k : ℕ) (eps : Error)
    (hk0 : 0 < k)
    (henv : 1 ≤ mainFormalEnvelope params k eps) :
    1 ≤ mainFormalError params k eps := by
  rw [mainFormalError_eq_envelope]
  have hk : (1 : Error) ≤ (k : Error) := by exact_mod_cast hk0
  have hm : (1 : Error) ≤ (params.m : Error) := by exact_mod_cast params.hm
  have hk2 : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
    simpa using one_le_pow₀ (n := (2 : ℕ)) hk
  have hm4 : (1 : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
    simpa using one_le_pow₀ (n := (4 : ℕ)) hm
  have hcoeff :
      (1 : Error) ≤ 100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    nlinarith
  have hcoeffNN :
      0 ≤ 100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  have hmul := mul_le_mul hcoeff henv (by norm_num : (0 : Error) ≤ 1) hcoeffNN
  simpa using hmul

/-- If `ε > 1`, then the final error envelope has already saturated past `1`.
This discharges the non-paper regime before invoking the paper's Step 8 cascade,
which assumes `ε ≤ 1`. -/
theorem mainFormalError_ge_one_of_one_lt_eps
    (params : Parameters) (k : ℕ) {eps : Error}
    (hk0 : 0 < k) (heps : 1 < eps) :
    1 ≤ mainFormalError params k eps := by
  have hepsPow : 1 ≤ Real.rpow eps (1 / (40000 : Error)) := by
    exact Real.one_le_rpow heps.le (by positivity)
  have hdqPowNN : 0 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
      (1 / (40000 : Error)) := by
    exact Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) params.q_cast_pos.le) _
  have hExpNN :
      0 ≤ Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))) :=
    Real.exp_nonneg _
  have henv : 1 ≤ mainFormalEnvelope params k eps := by
    unfold mainFormalEnvelope
    linarith
  exact mainFormalError_ge_one_of_one_le_envelope params k eps hk0 henv

/-- If `d > q`, then the final error envelope has already saturated past `1`.
Thus the nontrivial Step 8 branch may assume the paper's ambient `d/q ≤ 1`
regime. -/
theorem mainFormalError_ge_one_of_q_lt_d
    (params : Parameters) (k : ℕ) (eps : Error)
    (hk0 : 0 < k) (hepsNN : 0 ≤ eps)
    (hqd : (params.q : Error) < (params.d : Error)) :
    1 ≤ mainFormalError params k eps := by
  have hdq_gt_one : 1 < (params.d : Error) / (params.q : Error) := by
    exact (one_lt_div params.q_cast_pos).2 hqd
  have hdqPow : 1 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
      (1 / (40000 : Error)) := by
    exact Real.one_le_rpow hdq_gt_one.le (by positivity)
  have hepsPowNN : 0 ≤ Real.rpow eps (1 / (40000 : Error)) :=
    Real.rpow_nonneg hepsNN _
  have hExpNN :
      0 ≤ Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))) :=
    Real.exp_nonneg _
  have henv : 1 ≤ mainFormalEnvelope params k eps := by
    unfold mainFormalEnvelope
    linarith
  exact mainFormalError_ge_one_of_one_le_envelope params k eps hk0 henv

/-- In the non-vacuous branch of `mainFormal`, the standing scalar hypotheses of
Step 8 follow from the theorem's basic positivity data.

If either `ε > 1` or `d > q`, the final error `mainFormalError` is already at
least `1`, so `mainFormal_trivial_witness` handles the theorem. Hence under
`¬ 1 ≤ mainFormalError params k eps` we may safely enter the paper's cascade
regime `0 ≤ ε ≤ 1` and `d/q ≤ 1`. -/
theorem cascadeHypotheses_of_not_mainFormalError_ge_one
    {params : Parameters} {k : ℕ} {eps : Error}
    (hepsNN : 0 ≤ eps) (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    CascadeHypotheses params k eps where
  hk := by exact_mod_cast hk0
  hm := by exact_mod_cast params.hm
  hepsNN := hepsNN
  hepsOne := by
    by_contra heps_not
    exact hsmall (mainFormalError_ge_one_of_one_lt_eps params k hk0 (lt_of_not_ge heps_not))
  hdq := by
    by_contra hdq_not
    exact hsmall (mainFormalError_ge_one_of_q_lt_d params k eps hk0 hepsNN
      (lt_of_not_ge hdq_not))
  hqPos := params.q_cast_pos

/-- Scalar hypotheses for the Section 3 error cascade of `mainFormal`.

This record is intentionally scalar-only. It does not assert any measurement
transport. Its fields are precisely the hypotheses needed to invoke the already
formalized Step 8 bound `errorCascade_le_mainFormalError` on the
main-induction `ν` produced after symmetrization (paper lines 68--75). The
remaining proof of `mainFormal` must still derive these scalar side conditions
from the theorem hypotheses or route to the vacuous branch when they fail. -/
structure MainFormalCascadeScalars (params : Parameters) (eps : Error) (k : ℕ) : Prop where
  /-- Standing scalar regime for the paper's cascade estimates. -/
  cascadeHypotheses : CascadeHypotheses params k eps
  /-- Nonnegativity of the main-induction `ν` at `(3ε, 3ε, 3ε)`. -/
  inductionNu_nonneg : 0 ≤ mainFormalInductionNu params k eps
  /-- Paper line 71--73 coarsening of the main-induction `ν`. -/
  inductionNu_bound :
    mainFormalInductionNu params k eps ≤
      10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
        (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))

namespace MainFormalCascadeScalars

/-- Build the scalar data once the standing cascade hypotheses hold; the
main-induction `ν` nonnegativity and paper line 71--73 coarsening are discharged
by the checked scalar lemmas above. -/
theorem ofCascadeHypotheses {params : Parameters} {eps : Error} {k : ℕ}
    (h : CascadeHypotheses params k eps) :
    MainFormalCascadeScalars params eps k where
  cascadeHypotheses := h
  inductionNu_nonneg := mainFormalInductionNu_nonneg h
  inductionNu_bound := mainFormalInductionNu_bound h

/-- Build the scalar data in the non-vacuous branch of `mainFormal`.

The branch hypothesis `¬ 1 ≤ mainFormalError params k eps` rules out the
non-paper regimes `ε > 1` and `d > q`, while `hepsNN` and `hk0` supply the
remaining scalar positivity hypotheses. -/
theorem ofNontrivialMainFormal {params : Parameters} {eps : Error} {k : ℕ}
    (hepsNN : 0 ≤ eps) (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    MainFormalCascadeScalars params eps k :=
  ofCascadeHypotheses (cascadeHypotheses_of_not_mainFormalError_ge_one hepsNN hk0 hsmall)

/-- The paper's `σ`, built from the symmetrized main-induction `ν`. -/
noncomputable def sigma {params : Parameters} {eps : Error} {k : ℕ}
    (_scalars : MainFormalCascadeScalars params eps k) : Error :=
  cascadeSigma params k (mainFormalInductionNu params k eps)

/-- The paper's `ζ₁ = 2σ + 2√(3ε + 2σ) + md/q`. -/
noncomputable def zeta1 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) : Error :=
  cascadeZeta1 params eps scalars.sigma

/-- The formal Step 6 scalar
`ζ₂ = 200ζ₁^(1/4) + 42ζ₁^(1/8)`, widening the paper's printed coefficient
`40` to absorb the extra completion term. -/
noncomputable def zeta2 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) : Error :=
  cascadeZeta2 scalars.zeta1

/-- The paper's self-consistency scalar `ζ₃ = 6ζ₁ + 6ζ₂`. -/
noncomputable def zeta3 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) : Error :=
  cascadeZeta3 scalars.zeta1 scalars.zeta2

/-- The paper's point-consistency scalar `ζ₄ = 2σ + 2√(ζ₁ + ζ₃/2)`. -/
noncomputable def zeta4 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) : Error :=
  cascadeZeta4 scalars.sigma scalars.zeta1 scalars.zeta3

private theorem cascadeBounds {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    scalars.sigma ≤ mainFormalError params k eps ∧
      scalars.zeta1 ≤ mainFormalError params k eps ∧
      scalars.zeta2 ≤ mainFormalError params k eps ∧
      scalars.zeta3 ≤ 2 * mainFormalError params k eps ∧
      scalars.zeta4 ≤ mainFormalError params k eps := by
  exact errorCascade_le_mainFormalError
    (params := params) (k := k) (eps := eps)
    (ν := mainFormalInductionNu params k eps)
    (σ := scalars.sigma) (ζ₁ := scalars.zeta1)
    (ζ₂ := scalars.zeta2) (ζ₃ := scalars.zeta3)
    scalars.cascadeHypotheses scalars.inductionNu_nonneg scalars.inductionNu_bound
    rfl rfl rfl rfl

/-- Nonnegativity of the native cascade `σ`. -/
theorem sigma_nonneg {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    0 ≤ scalars.sigma := by
  unfold sigma cascadeSigma
  positivity [scalars.inductionNu_nonneg]

/-- Nonnegativity of the native cascade `ζ₁`. -/
theorem zeta1_nonneg {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    0 ≤ scalars.zeta1 := by
  have hσ : 0 ≤ scalars.sigma := sigma_nonneg scalars
  have hdq : 0 ≤ (params.d : Error) / (params.q : Error) :=
    scalars.cascadeHypotheses.dqNN
  unfold zeta1 cascadeZeta1
  positivity [hσ, scalars.cascadeHypotheses.hepsNN, hdq]

/-- Step 8 absorption for the native `ζ₁` target. -/
theorem zeta1_le_mainFormalError {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    scalars.zeta1 ≤ mainFormalError params k eps :=
  (cascadeBounds scalars).2.1

/-- In the non-vacuous branch, the cascade scalar `ζ₁` lies in the unit interval. -/
theorem zeta1_le_one_of_not_mainFormalError_ge_one
    {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    scalars.zeta1 ≤ 1 := by
  exact le_of_lt <|
    (zeta1_le_mainFormalError scalars).trans_lt (lt_of_not_ge hsmall)

/-- The formal `ζ₂` scalar absorbs the literal Step 6 orthonormalize-and-complete
error in the non-vacuous branch. -/
theorem orthonormalizeAndCompleteError_zeta1_le_zeta2
    {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1 ≤
      scalars.zeta2 := by
  have hζ0 : 0 ≤ scalars.zeta1 := zeta1_nonneg scalars
  have hζ1 : scalars.zeta1 ≤ 1 :=
    zeta1_le_one_of_not_mainFormalError_ge_one scalars hsmall
  simpa [zeta2, cascadeZeta2] using
    MakingMeasurementsProjective.orthonormalizeAndCompleteError_le_absorbedZeta2
      (ζ := scalars.zeta1) hζ0 hζ1

/-- Step 8 absorption for the native `ζ₄` point-consistency targets. -/
theorem zeta4_le_mainFormalError {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    scalars.zeta4 ≤ mainFormalError params k eps :=
  (cascadeBounds scalars).2.2.2.2

/-- Step 8 absorption for the native `ζ₃/2` self-consistency target. -/
theorem zeta3_div_two_le_mainFormalError {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    scalars.zeta3 / 2 ≤ mainFormalError params k eps := by
  have hzeta3 := (cascadeBounds scalars).2.2.2.1
  linarith

end MainFormalCascadeScalars

end Test

end MIPStarRE.LDT
