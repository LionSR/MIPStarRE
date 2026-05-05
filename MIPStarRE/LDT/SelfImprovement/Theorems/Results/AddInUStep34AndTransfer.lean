import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep12
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness

/-!
# Add-in-u variance-bound conversions, factored Step 3/4 CS, assembly and transfer

Variance-bound conversions for Q₂→Q₃ / Q₃→Q₄, the factored
`add_in_u_cs_chain_q2_q3_factored_cs` and
`add_in_u_cs_chain_q3_q4_factored_cs` Cauchy–Schwarz lemmas, the
available Q₂→Q₃ and Q₃→Q₄ self-energy factor bounds, the four-step chain
assembly, arithmetic absorption `2√(2δ) + 2√ζ ≤ 4√ζ`, and the
projection-simplified diagonal transfer.

## Contents

- **Variance-bound conversions** — `add_in_u_cs_chain_q2_q3_abs_le_sqrt_of_sq_le`,
  `_le_sqrt_of_factor_bounds`, and the Q₃→Q₄ analogues.
- **add_in_u_cs_chain_q2_q3_factored_cs** and
  **add_in_u_cs_chain_q3_q4_factored_cs** — the factored CS lemmas
  `|Q₂−Q₃| ≤ √D₁ · √D₂` and `|Q₃−Q₄| ≤ √D₁ · √D₂`.
- **addInU_selected_cs_chain_step3/step4_abs_le_sqrt_globalVarianceDeviation_sum**
  — the selection-parametrized Step 3/4 bounds used by the off-diagonal
  point-consistency application.
- **add_in_u_cs_chain_q2_q3_self_energy_factor_le_one** and
  **add_in_u_cs_chain_q3_q4_self_energy_factor_le_one** — the self-energy
  factors bounded by `1` in the two global-variance CS paths.
- **add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum** and
  **add_in_u_cs_chain_q3_q4_variance_factor_le_globalVarianceDeviation_sum** —
  comparison of the variance factors with the summed global-variance deviation.
- **add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum** and
  **add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum** — the raw
  global-variance CS estimates after the factor bounds have been applied.
- **GlobalVariance endpoint bridges** —
  `_le_sqrt_of_globalVarianceDeviation_sum_le` and
  `add_in_u_cs_chain_global_variance_steps_of_sum_bound / _of_local_sum_bound`
  upgrading raw CS estimates to `√ζ` bounds.
- **Closed Step 3/4 wrappers** —
  `add_in_u_cs_chain_global_variance_steps_of_sum_bound_from_factor_bounds`,
  `add_in_u_cs_chain_global_variance_steps_of_local_sum_bound_from_factor_bounds`,
  and `add_in_u_simplified_transfer_of_cs_chain_local_variance_form`.
- **Self-consistency/local-variance wrapper** —
  `add_in_u_simplified_transfer_of_cs_chain_selfConsistency_local_variance_form`.
- **add_in_u_simplified_transfer_of_cs_chain** — the four-step chain
  assembly: given four `|Qᵢ−Qⱼ| ≤ ηᵢⱼ` bounds summing to `≤ addInUError`,
  yields the projection-simplified transfer.
- **add_in_u_selected_transfer_of_cs_chain** — the same four-step assembly
  before specializing the add-in-u outcome family and selection.
- **Arithmetic absorption** — `two_mul_delta_le_selfImprovementVarianceError`
  and `two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError`
  (paper lines 341–342).
- **add_in_u_simplified_transfer_of_cs_chain_sqrt_form** — wrapper
  composing the CS chain with arithmetic absorption.
- **selfConsistencyDiagonalAddInU_of_simplifiedTransfer** — specialization
  to the projection-simplified scalar transfer hypothesis.
- **helper_mass_sub_release_eq_polynomial_off_diagonal** — exact expansion of
  the helper mass minus the released diagonal right-hand side as the
  off-diagonal polynomial-pair contribution.

## References

- `references/ldt-paper/self_improvement.tex` lines 299–343
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/


namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma le_sqrt_of_factor_bounds_right
    {a D₁ D₂ s : Error}
    (hCS : a ≤ Real.sqrt D₁ * Real.sqrt D₂)
    (hD₁_le : D₁ ≤ s)
    (hD₂_le_one : D₂ ≤ 1) :
    a ≤ Real.sqrt s := by
  have hsqrt_D₂ : Real.sqrt D₂ ≤ 1 := Real.sqrt_le_one.mpr hD₂_le_one
  have hsqrt_D₁ : Real.sqrt D₁ ≤ Real.sqrt s := Real.sqrt_le_sqrt hD₁_le
  calc
    a ≤ Real.sqrt D₁ * Real.sqrt D₂ := hCS
    _ ≤ Real.sqrt D₁ * 1 :=
          mul_le_mul_of_nonneg_left hsqrt_D₂ (Real.sqrt_nonneg _)
    _ = Real.sqrt D₁ := mul_one _
    _ ≤ Real.sqrt s := hsqrt_D₁

private lemma le_sqrt_of_factor_bounds_left
    {a D₁ D₂ s : Error}
    (hCS : a ≤ Real.sqrt D₁ * Real.sqrt D₂)
    (hD₁_le_one : D₁ ≤ 1)
    (hD₂_le : D₂ ≤ s) :
    a ≤ Real.sqrt s := by
  have hsqrt_D₁ : Real.sqrt D₁ ≤ 1 := Real.sqrt_le_one.mpr hD₁_le_one
  have hsqrt_D₂ : Real.sqrt D₂ ≤ Real.sqrt s := Real.sqrt_le_sqrt hD₂_le
  calc
    a ≤ Real.sqrt D₁ * Real.sqrt D₂ := hCS
    _ ≤ 1 * Real.sqrt D₂ :=
          mul_le_mul_of_nonneg_right hsqrt_D₁ (Real.sqrt_nonneg _)
    _ = Real.sqrt D₂ := one_mul _
    _ ≤ Real.sqrt s := hsqrt_D₂

/-! ### Add-in-u variance-bound conversions

The following four lemmas are conditional real-valued conversions for the
`Q₂ → Q₃` and `Q₃ → Q₄` add-in-u steps.  They do not prove the
operator-theoretic Cauchy--Schwarz estimates from
`references/ldt-paper/self_improvement.tex`, lines 299--340.  Instead, they
convert either a squared real bound or a factored product of square-root bounds
into the absolute-value square-root shape used by the surrounding scalar chain.

The hypotheses `hsq`, `hCS`, and `hD*_le*` are the places where future
operator-level arguments must supply the Cauchy--Schwarz, submeasurement
contraction, and total-mass estimates.  In particular, `T` is a submeasurement
in these statements; any `≤ 1` input corresponds to a `total_le_one`-style
bound rather than a measurement equality. -/

/-- Convert a squared `Q₂ → Q₃` real bound to an absolute-value sqrt bound.

This lemma is only the `Real.abs_le_sqrt` conversion.  The hypothesis `hsq`
must already contain any operator Cauchy--Schwarz and submeasurement estimates
needed to prove the squared bound. -/
lemma add_in_u_cs_chain_q2_q3_abs_le_sqrt_of_sq_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (hsq :
      (addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T) ^ 2 ≤
        ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  Real.abs_le_sqrt hsq

/-- Convert factored `Q₂ → Q₃` sqrt bounds to the summed-deviation sqrt bound.

This lemma assumes the Cauchy--Schwarz product bound as `hCS`, a bound on the
first factor by the summed independent-points deviation, and a `≤ 1` bound on
the second factor.  The proof is purely real-valued; the submeasurement and
operator content belongs in the hypotheses. -/
lemma add_in_u_cs_chain_q2_q3_le_sqrt_of_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (D₁ D₂ : Error)
    (hCS :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt D₁ * Real.sqrt D₂)
    (hD₁_le :
      D₁ ≤ ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g)
    (hD₂_le_one : D₂ ≤ 1) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  le_sqrt_of_factor_bounds_right hCS hD₁_le hD₂_le_one

/-- Convert a squared `Q₃ → Q₄` real bound to an absolute-value sqrt bound.

This lemma is only the `Real.abs_le_sqrt` conversion.  The hypothesis `hsq`
must already contain any operator Cauchy--Schwarz and submeasurement estimates
needed to prove the squared bound. -/
lemma add_in_u_cs_chain_q3_q4_abs_le_sqrt_of_sq_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (hsq :
      (addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T) ^ 2 ≤
        ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  Real.abs_le_sqrt hsq

/-- Convert factored `Q₃ → Q₄` sqrt bounds to the summed-deviation sqrt bound.

This lemma assumes the Cauchy--Schwarz product bound as `hCS`, a `≤ 1` bound
on the first factor, and a bound on the second factor by the summed
independent-points deviation.  The proof is purely real-valued; the
submeasurement and operator content belongs in the hypotheses. -/
lemma add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (D₁ D₂ : Error)
    (hCS :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt D₁ * Real.sqrt D₂)
    (hD₁_le_one : D₁ ≤ 1)
    (hD₂_le :
      D₂ ≤ ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  le_sqrt_of_factor_bounds_left hCS hD₁_le_one hD₂_le

/-- Weighted Cauchy--Schwarz for the non-selected add-in-`u` Step 3/4
summands.

The non-selected Step 3 and Step 4 estimates use the same finite inequality
over independent point pairs and polynomial outcomes.  This helper fixes that
common summation structure, leaving the two applications to supply only their
step-specific summands and pointwise operator Cauchy--Schwarz estimates. -/
private theorem addInU_weighted_cauchy_schwarz
    (params : Parameters) [FieldModel params.q]
    (t x y : Point params × Point params → Polynomial params → Error)
    (ht : ∀ uv h, |t uv h| ≤ Real.sqrt (x uv h) * Real.sqrt (y uv h))
    (hx : ∀ uv h, 0 ≤ x uv h)
    (hy : ∀ uv h, 0 ≤ y uv h) :
    |avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : Polynomial params, t uv h)| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, x uv h)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, y uv h)) := by
  exact
    MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz
      (Question := Point params × Point params) (Outcome := Polynomial params)
      (uniformDistribution (Point params × Point params))
      (t := t) (x := x) (y := y) ht hx hy

/-- Factored operator Cauchy--Schwarz bound for the `Q₂ → Q₃` add-in-`u` step.

Applies the bipartite-tensor sandwich Cauchy--Schwarz primitive
`ev_opTensor_sandwich_abs_le_sqrt` at each `(u, v, h)` and lifts the pointwise
estimate through the avgOver-finset Cauchy--Schwarz inequality. The two factors
are the variance term
`(A^v_{h(v)} - A^u_{h(u)}) · H^u_h · (A^v_{h(v)} - A^u_{h(u)})`
and the self-energy term `A^v_{h(v)} · H^u_h · A^v_{h(v)}`.

The paper presents this step before the fiberwise `o`-sum is collapsed, using
the middle operator `M^u_o`.  The Lean chain has already reindexed that sum by
`o = h(u)`, so the middle operator is the helper outcome
`H^u_h = (sandwichedPolynomialSubMeasAt params strategy T u).outcome h`.

This is the operator Cauchy--Schwarz part of `eq:change-one-cauchy-schwarz` in
`references/ldt-paper/self_improvement.tex`, lines 306--311. It does not yet
identify the first factor with the summed global-variance deviation, nor bound
the second factor by `1`; those factor estimates are supplied below and then
fed into `add_in_u_cs_chain_q2_q3_le_sqrt_of_factor_bounds`. -/
theorem add_in_u_cs_chain_q2_q3_factored_cs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
            let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
            ev strategy.state
              (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h)))) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params,
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
            let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
            ev strategy.state
              (opTensor (Av * Mh * Av) (T.outcome h)))) := by
  classical
  rw [addInU_cs_chain_step3_diff_eq params strategy T]
  refine addInU_weighted_cauchy_schwarz params
    (t := fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
      ev strategy.state (opTensor ((Av - Au) * Mh * Av) (T.outcome h)))
    (x := fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
      ev strategy.state
        (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h)))
    (y := fun uv h =>
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
      ev strategy.state (opTensor (Av * Mh * Av) (T.outcome h))) ?_ ?_ ?_
  · -- Pointwise CS bound at each `(u, v, h)`.
    intro uv h
    set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
    set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
    have hMh_pos : 0 ≤ Mh :=
      (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h
    have hTh_pos : 0 ≤ T.outcome h := T.outcome_pos h
    have hAu_herm : Auᴴ = Au :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
    have hAv_herm : Avᴴ = Av :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
    have hX_herm : (Av - Au)ᴴ = Av - Au := by
      rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
    have hsandwich :=
      ev_opTensor_sandwich_abs_le_sqrt strategy.state (Av - Au) Av Mh
        (T.outcome h) hMh_pos hTh_pos
    simp only [hX_herm, hAv_herm] at hsandwich
    exact hsandwich
  · -- `0 ≤ x uv h`: the variance-style diagonal expectation is nonnegative.
    intro uv h
    set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
    set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
    have hMh_pos : 0 ≤ Mh :=
      (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h
    have hTh_pos : 0 ≤ T.outcome h := T.outcome_pos h
    have hAu_herm : Auᴴ = Au :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
    have hAv_herm : Avᴴ = Av :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
    have hX_herm : (Av - Au)ᴴ = Av - Au := by
      rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
    have hXMhX_pos : 0 ≤ (Av - Au) * Mh * (Av - Au) := by
      have :=
        ((Matrix.nonneg_iff_posSemidef.mp hMh_pos).conjTranspose_mul_mul_same
          (Av - Au)).nonneg
      rwa [hX_herm] at this
    exact ev_nonneg_of_psd strategy.state _ (opTensor_nonneg hXMhX_pos hTh_pos)
  · -- `0 ≤ y uv h`: the self-energy expectation is nonnegative.
    intro uv h
    set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
    set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
    have hMh_pos : 0 ≤ Mh :=
      (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h
    have hTh_pos : 0 ≤ T.outcome h := T.outcome_pos h
    have hAv_herm : Avᴴ = Av :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
    have hAvMhAv_pos : 0 ≤ Av * Mh * Av := by
      have :=
        ((Matrix.nonneg_iff_posSemidef.mp hMh_pos).conjTranspose_mul_mul_same Av).nonneg
      rwa [hAv_herm] at this
    exact ev_nonneg_of_psd strategy.state _ (opTensor_nonneg hAvMhAv_pos hTh_pos)

/-- Factored operator Cauchy–Schwarz bound for the `Q₃ → Q₄` add-in-`u` step.

Applies the bipartite-tensor sandwich Cauchy–Schwarz primitive
`ev_opTensor_sandwich_abs_le_sqrt` (PR #1121) at each `(u, v, h)` and lifts the
bound through the avgOver-finset Cauchy–Schwarz `weightedFinsetCauchySchwarz`.
The expressions
`A^u_{h(u)} · H^u_h · A^u_{h(u)}` and
`(A^v_{h(v)} − A^u_{h(u)}) · H^u_h · (A^v_{h(v)} − A^u_{h(u)})`
are PSD by the conjugate-transpose-mul-mul-same monotonicity of the
projection-sandwich `H^u_h = A^u_{h(u)} · T_h · A^u_{h(u)}`.

This is the operator/real Cauchy–Schwarz fragment of `eq:change-another` in
`references/ldt-paper/self_improvement.tex`, lines 326–332.  Combined with
sub-measurement-monotonicity on the first factor (`≤ 1`) and the
independent-points global-variance identification of the second factor
(`= ∑ g, globalVarianceDeviationAtPolynomial …`), this feeds
`add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds` and the
`add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le` bridge
from PR #1083. -/
theorem add_in_u_cs_chain_q3_q4_factored_cs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
            let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
            ev strategy.state (opTensor (Au * Mh * Au) (T.outcome h)))) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
            let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
            ev strategy.state
              (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h)))) := by
  classical
  rw [addInU_cs_chain_step4_diff_eq params strategy T]
  refine addInU_weighted_cauchy_schwarz params
    (t := fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
      ev strategy.state (opTensor (Au * Mh * (Av - Au)) (T.outcome h)))
    (x := fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
      ev strategy.state (opTensor (Au * Mh * Au) (T.outcome h)))
    (y := fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
      ev strategy.state
        (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h))) ?_ ?_ ?_
  · -- Pointwise CS bound at each `(u, v, h)`.
    intro uv h
    set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
    set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
    have hMh_pos : 0 ≤ Mh :=
      (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h
    have hTh_pos : 0 ≤ T.outcome h := T.outcome_pos h
    have hAu_herm : Auᴴ = Au :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
    have hAv_herm : Avᴴ = Av :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
    have hY_herm : (Av - Au)ᴴ = Av - Au := by
      rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
    have hsandwich :=
      ev_opTensor_sandwich_abs_le_sqrt strategy.state Au (Av - Au) Mh
        (T.outcome h) hMh_pos hTh_pos
    simp only [hAu_herm, hY_herm] at hsandwich
    exact hsandwich
  · -- `0 ≤ x uv h`: the diagonal sandwich expectation is nonneg.
    intro uv h
    set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
    have hMh_pos : 0 ≤ Mh :=
      (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h
    have hTh_pos : 0 ≤ T.outcome h := T.outcome_pos h
    have hAu_herm : Auᴴ = Au :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
    have hAuMhAu_pos : 0 ≤ Au * Mh * Au := by
      have :=
        ((Matrix.nonneg_iff_posSemidef.mp hMh_pos).conjTranspose_mul_mul_same Au).nonneg
      rwa [hAu_herm] at this
    exact ev_nonneg_of_psd strategy.state _ (opTensor_nonneg hAuMhAu_pos hTh_pos)
  · -- `0 ≤ y uv h`: the variance-style diagonal expectation is nonneg.
    intro uv h
    set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
    set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
    have hMh_pos : 0 ≤ Mh :=
      (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos h
    have hTh_pos : 0 ≤ T.outcome h := T.outcome_pos h
    have hAu_herm : Auᴴ = Au :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
    have hAv_herm : Avᴴ = Av :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
    have hY_herm : (Av - Au)ᴴ = Av - Au := by
      rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
    have hYMhY_pos : 0 ≤ (Av - Au) * Mh * (Av - Au) := by
      have :=
        ((Matrix.nonneg_iff_posSemidef.mp hMh_pos).conjTranspose_mul_mul_same
          (Av - Au)).nonneg
      rwa [hY_herm] at this
    exact ev_nonneg_of_psd strategy.state _ (opTensor_nonneg hYMhY_pos hTh_pos)

/-- Selected-support weighted Cauchy--Schwarz for the add-in-`u` Step 3/4
summands.

The selected Step 3 and Step 4 estimates use the same finite inequality: the
summands are restricted to the selected pairs `S_u`, and are extended by zero
outside this support.  This helper fixes the distribution and the selected
support, leaving only the three summands and their pointwise estimates to be
specified by the two applications. -/
private theorem addInU_selected_weighted_cauchy_schwarz
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (S : AddInUSelection params Outcome)
    (t x y : Point params × Point params → Outcome × Polynomial params → Error)
    (ht :
      ∀ uv ah, ah ∈ addInUSelectionPairs params S uv.1 →
        |t uv ah| ≤ Real.sqrt (x uv ah) * Real.sqrt (y uv ah))
    (hx : ∀ uv ah, ah ∈ addInUSelectionPairs params S uv.1 → 0 ≤ x uv ah)
    (hy : ∀ uv ah, ah ∈ addInUSelectionPairs params S uv.1 → 0 ≤ y uv ah) :
    |avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then t uv ah else 0)| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then x uv ah else 0)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then y uv ah else 0)) := by
  classical
  exact
    MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz_on_selectedSupport
      (𝒟 := uniformDistribution (Point params × Point params))
      (selected := fun uv ah => ah ∈ addInUSelectionPairs params S uv.1)
      (t := t) (x := x) (y := y) ht hx hy

/-- Selected factored Cauchy--Schwarz bound for the `Q₂ → Q₃` add-in-`u` step.

This is the selection-parametrized analogue of
`add_in_u_cs_chain_q2_q3_factored_cs`.  The summation is over all pairs
`(o,h)`, with the terms outside the selected set `S_u` set to zero; this form is
convenient for the finite Cauchy--Schwarz lemma and is equivalent to the
fiberwise selected sum appearing in the paper. -/
private theorem addInU_selected_cs_chain_step3_factored_cs
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state
                (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
            else 0)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state
                (opTensor (Av * Moh * Av) (T.outcome ah.2))
            else 0)) := by
  classical
  rw [addInU_selected_cs_chain_step3_diff_eq params strategy M T S]
  simpa using
    addInU_selected_weighted_cauchy_schwarz (Outcome := Outcome) params S
      (t := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor ((Av - Au) * Moh * Av) (T.outcome ah.2)))
      (x := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2)))
      (y := fun uv ah =>
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor (Av * Moh * Av) (T.outcome ah.2)))
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hX_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hsandwich :=
          ev_opTensor_sandwich_abs_le_sqrt strategy.state (Av - Au) Av Moh
            (T.outcome ah.2) hMoh_pos hTh_pos
        simpa only [hX_herm, hAv_herm] using hsandwich)
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hX_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hXMohX_pos : 0 ≤ (Av - Au) * Moh * (Av - Au) := by
          have :=
            ((Matrix.nonneg_iff_posSemidef.mp hMoh_pos).conjTranspose_mul_mul_same
              (Av - Au)).nonneg
          rwa [hX_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hXMohX_pos hTh_pos))
      (by
        intro uv ah _hmem
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hAvMohAv_pos : 0 ≤ Av * Moh * Av := by
          have :=
            ((Matrix.nonneg_iff_posSemidef.mp hMoh_pos).conjTranspose_mul_mul_same
              Av).nonneg
          rwa [hAv_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hAvMohAv_pos hTh_pos))

/-- Selected factored Cauchy--Schwarz bound for the `Q₃ → Q₄` add-in-`u` step.

This is the selection-parametrized analogue of
`add_in_u_cs_chain_q3_q4_factored_cs`; as in
`addInU_selected_cs_chain_step3_factored_cs`, terms outside the selected set
are represented by zeros in the finite Cauchy--Schwarz sum. -/
private theorem addInU_selected_cs_chain_step4_factored_cs
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state (opTensor (Au * Moh * Au) (T.outcome ah.2))
            else 0)) *
      Real.sqrt
        (avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ ah : Outcome × Polynomial params,
            if ah ∈ addInUSelectionPairs params S uv.1 then
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
              let Moh := (M uv.1).outcome ah.1
              ev strategy.state
                (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
            else 0)) := by
  classical
  rw [addInU_selected_cs_chain_step4_diff_eq params strategy M T S]
  simpa using
    addInU_selected_weighted_cauchy_schwarz (Outcome := Outcome) params S
      (t := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor (Au * Moh * (Av - Au)) (T.outcome ah.2)))
      (x := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state (opTensor (Au * Moh * Au) (T.outcome ah.2)))
      (y := fun uv ah =>
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2)))
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hY_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hsandwich :=
          ev_opTensor_sandwich_abs_le_sqrt strategy.state Au (Av - Au) Moh
            (T.outcome ah.2) hMoh_pos hTh_pos
        simpa only [hAu_herm, hY_herm] using hsandwich)
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAuMohAu_pos : 0 ≤ Au * Moh * Au := by
          have :=
            ((Matrix.nonneg_iff_posSemidef.mp hMoh_pos).conjTranspose_mul_mul_same
              Au).nonneg
          rwa [hAu_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hAuMohAu_pos hTh_pos))
      (by
        intro uv ah _hmem
        set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        set Moh := (M uv.1).outcome ah.1
        have hMoh_pos : 0 ≤ Moh := (M uv.1).outcome_pos ah.1
        have hTh_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
        have hAu_herm : Auᴴ = Au :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas
            (ah.2 uv.1)
        have hAv_herm : Avᴴ = Av :=
          SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas
            (ah.2 uv.2)
        have hY_herm : (Av - Au)ᴴ = Av - Au := by
          rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        have hYMohY_pos : 0 ≤ (Av - Au) * Moh * (Av - Au) := by
          have :=
            ((Matrix.nonneg_iff_posSemidef.mp hMoh_pos).conjTranspose_mul_mul_same
              (Av - Au)).nonneg
          rwa [hY_herm] at this
        exact ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg hYMohY_pos hTh_pos))

/-- A selected sandwich tensor sum is bounded by replacing the selected
submeasurement mass with the identity.

For a fixed point `u`, the selected pairs are a subcollection of
`Outcome × Polynomial params`.  Summing over all pairs, the `Outcome`-mass
collapses to `(M u).total`, and the submeasurement inequality
`(M u).total ≤ I` gives the displayed upper bound. -/
private lemma addInU_selected_sandwich_tensor_if_sum_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (u : Point params)
    (X : Polynomial params → MIPStarRE.Quantum.Op ι)
    (hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h) :
    (∑ ah : Outcome × Polynomial params,
      if ah ∈ addInUSelectionPairs params S u then
        opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2)
      else 0) ≤
      ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := by
  classical
  let s := addInUSelectionPairs params S u
  let f : Outcome × Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun ah =>
    opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2)
  have hf_nonneg : ∀ ah : Outcome × Polynomial params, 0 ≤ f ah := by
    intro ah
    have hM_pos : 0 ≤ (M u).outcome ah.1 := (M u).outcome_pos ah.1
    have hT_pos : 0 ≤ T.outcome ah.2 := T.outcome_pos ah.2
    have hleft_pos : 0 ≤ X ah.2 * (M u).outcome ah.1 * X ah.2 := by
      have :=
        ((Matrix.nonneg_iff_posSemidef.mp hM_pos).conjTranspose_mul_mul_same
          (X ah.2)).nonneg
      rwa [hX_herm ah.2] at this
    exact opTensor_nonneg hleft_pos hT_pos
  have hif_eq :
      (∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S u then f ah else 0) =
        ∑ ah ∈ s, f ah := by
    simp [s]
  have hselected_le_univ :
      ∑ ah ∈ s, f ah ≤ ∑ ah : Outcome × Polynomial params, f ah :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro ah _
        exact Finset.mem_univ ah)
      (by
        intro ah _ _
        exact hf_nonneg ah)
  have huniv_eq :
      (∑ ah : Outcome × Polynomial params, f ah) =
        ∑ h : Polynomial params,
          opTensor (X h * (M u).total * X h) (T.outcome h) := by
    calc
      (∑ ah : Outcome × Polynomial params, f ah)
          = ∑ o : Outcome, ∑ h : Polynomial params,
              opTensor (X h * (M u).outcome o * X h) (T.outcome h) := by
              rw [Fintype.sum_prod_type]
      _ = ∑ h : Polynomial params, ∑ o : Outcome,
            opTensor (X h * (M u).outcome o * X h) (T.outcome h) := by
            rw [Finset.sum_comm]
      _ = ∑ h : Polynomial params,
            opTensor (X h * (M u).total * X h) (T.outcome h) := by
            refine Finset.sum_congr rfl ?_
            intro h _
            calc
              ∑ o : Outcome,
                  opTensor (X h * (M u).outcome o * X h) (T.outcome h)
                  = opTensor
                      (∑ o : Outcome, X h * (M u).outcome o * X h)
                      (T.outcome h) := by
                    rw [opTensor_sum_left_univ]
              _ = opTensor (X h * (M u).total * X h) (T.outcome h) := by
                    congr 1
                    rw [← (M u).sum_eq_total, Finset.mul_sum, Finset.sum_mul]
  have htotal_le :
      ∑ h : Polynomial params,
          opTensor (X h * (M u).total * X h) (T.outcome h) ≤
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := by
    refine Finset.sum_le_sum ?_
    intro h _
    have hleft_le : X h * (M u).total * X h ≤ X h * 1 * X h :=
      MIPStarRE.Quantum.sandwich_mono (hX_herm h) (M u).total_le_one
    simpa using opTensor_mono_left hleft_le (T.outcome_pos h)
  calc
    (∑ ah : Outcome × Polynomial params,
      if ah ∈ addInUSelectionPairs params S u then
        opTensor (X ah.2 * (M u).outcome ah.1 * X ah.2) (T.outcome ah.2)
      else 0)
        = ∑ ah ∈ s, f ah := hif_eq
    _ ≤ ∑ ah : Outcome × Polynomial params, f ah := hselected_le_univ
    _ = ∑ h : Polynomial params,
          opTensor (X h * (M u).total * X h) (T.outcome h) := huniv_eq
    _ ≤ ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := htotal_le

private lemma addInU_selected_cs_chain_self_energy_factor_le_one_at
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (p : Point params × Point params → Point params) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state (opTensor (A * Moh * A) (T.outcome ah.2))
        else 0) ≤ 1 := by
  classical
  have hpointwise : ∀ uv : Point params × Point params,
      (∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state (opTensor (A * Moh * A) (T.outcome ah.2))
        else 0) ≤ 1 := by
    intro uv
    let X : Polynomial params → MIPStarRE.Quantum.Op ι :=
      fun h => pointConditionedOutcomeOperatorAtPolynomial params strategy h (p uv)
    have hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h := by
      intro h
      exact SubMeas.outcome_hermitian (strategy.pointMeasurement (p uv)).toSubMeas
        (h (p uv))
    have hsum_le :
        (∑ ah : Outcome × Polynomial params,
          if ah ∈ addInUSelectionPairs params S uv.1 then
            opTensor (X ah.2 * (M uv.1).outcome ah.1 * X ah.2) (T.outcome ah.2)
          else 0) ≤
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) :=
      addInU_selected_sandwich_tensor_if_sum_le params M T S uv.1 X hX_herm
    have hright_le_one :
        (∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h)) ≤
          (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      calc
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h)
            = ∑ h : Polynomial params, opTensor (X h) (T.outcome h) := by
                refine Finset.sum_congr rfl ?_
                intro h _
                have hproj : X h * X h = X h := by
                  dsimp [X, pointConditionedOutcomeOperatorAtPolynomial]
                  exact (strategy.pointMeasurement (p uv)).proj (h (p uv))
                rw [hproj]
        _ ≤ ∑ h : Polynomial params,
              opTensor (1 : MIPStarRE.Quantum.Op ι) (T.outcome h) := by
              refine Finset.sum_le_sum ?_
              intro h _
              exact opTensor_mono_left
                ((strategy.pointMeasurement (p uv)).toSubMeas.outcome_le_one (h (p uv)))
                (T.outcome_pos h)
        _ = rightTensor (ι₁ := ι) T.total := by
              rw [← T.sum_eq_total, ← opTensor_sum_right_univ]
        _ ≤ 1 := rightTensor_le_one (ι₁ := ι) T.total_le_one
    have hop_le :
        (∑ ah : Outcome × Polynomial params,
          if ah ∈ addInUSelectionPairs params S uv.1 then
            let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
            let Moh := (M uv.1).outcome ah.1
            opTensor (A * Moh * A) (T.outcome ah.2)
          else 0) ≤ 1 := by
      simpa [X] using le_trans hsum_le hright_le_one
    calc
      (∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let A := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 (p uv)
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state (opTensor (A * Moh * A) (T.outcome ah.2))
        else 0)
          = ev strategy.state
              (∑ ah : Outcome × Polynomial params,
                if ah ∈ addInUSelectionPairs params S uv.1 then
                  let A := pointConditionedOutcomeOperatorAtPolynomial
                    params strategy ah.2 (p uv)
                  let Moh := (M uv.1).outcome ah.1
                  opTensor (A * Moh * A) (T.outcome ah.2)
                else 0) := by
              rw [ev_finset_sum]
              refine Finset.sum_congr rfl ?_
              intro ah _
              by_cases hmem : ah ∈ addInUSelectionPairs params S uv.1
              · simp [hmem]
              · simp [hmem, ev_zero]
      _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) :=
            ev_mono strategy.state _ _ hop_le
      _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized
  exact avgOver_uniform_le_of_pointwise_le _ 1 zero_le_one hpointwise

/-- Selected self-energy factor `≤ 1` for the `Q₂ → Q₃` factored
Cauchy--Schwarz bound. -/
private lemma addInU_selected_cs_chain_step3_self_energy_factor_le_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state (opTensor (Av * Moh * Av) (T.outcome ah.2))
        else 0) ≤ 1 := by
  classical
  simpa using
    addInU_selected_cs_chain_self_energy_factor_le_one_at
      params strategy M T S (fun uv : Point params × Point params => uv.2)

/-- Selected self-energy factor `≤ 1` for the `Q₃ → Q₄` factored
Cauchy--Schwarz bound. -/
private lemma addInU_selected_cs_chain_step4_self_energy_factor_le_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state (opTensor (Au * Moh * Au) (T.outcome ah.2))
        else 0) ≤ 1 := by
  classical
  simpa using
    addInU_selected_cs_chain_self_energy_factor_le_one_at
      params strategy M T S (fun uv : Point params × Point params => uv.1)

/-- The selected Step 3/4 variance factor is bounded by the summed
global-variance deviation.

The selected middle operators form a submeasurement after summing over their
outcome coordinate, so the selected sandwich is dominated by the square of
`A^v_{h(v)} - A^u_{h(u)}`.  Averaging over independent points identifies the
result with the global-variance deviation sum. -/
private lemma addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
        else 0) ≤
      ∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
  classical
  let varianceTerm : Point params × Point params → Error := fun uv =>
    ∑ ah : Outcome × Polynomial params,
      if ah ∈ addInUSelectionPairs params S uv.1 then
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
      else 0
  let squaredTerm : Point params × Point params → Polynomial params → Error :=
    fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state (opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h))
  have hpointwise : ∀ uv : Point params × Point params,
      varianceTerm uv ≤ ∑ h : Polynomial params, squaredTerm uv h := by
    intro uv
    let X : Polynomial params → MIPStarRE.Quantum.Op ι := fun h =>
      pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 -
        pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    have hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h := by
      intro h
      have hAu_herm :
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1)ᴴ =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
      have hAv_herm :
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)ᴴ =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
      dsimp [X]
      rw [Matrix.conjTranspose_sub, hAv_herm, hAu_herm]
    have hop_le :
        (∑ ah : Outcome × Polynomial params,
          if ah ∈ addInUSelectionPairs params S uv.1 then
            opTensor (X ah.2 * (M uv.1).outcome ah.1 * X ah.2) (T.outcome ah.2)
          else 0) ≤
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) :=
      addInU_selected_sandwich_tensor_if_sum_le params M T S uv.1 X hX_herm
    have hoperator_to_squared :
        (∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h)) =
          ∑ h : Polynomial params,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
            opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h) := by
      refine Finset.sum_congr rfl ?_
      intro h _
      set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      have hAu_herm : Auᴴ = Au :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
      have hAv_herm : Avᴴ = Av :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
      have hsq : (Av - Au) * (Av - Au) = ((Au - Av)ᴴ) * (Au - Av) := by
        rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
        noncomm_ring
      simpa [X, Au, Av] using congrArg (fun Z => opTensor Z (T.outcome h)) hsq
    calc
      varianceTerm uv
          = ev strategy.state
              (∑ ah : Outcome × Polynomial params,
                if ah ∈ addInUSelectionPairs params S uv.1 then
                  let Au := pointConditionedOutcomeOperatorAtPolynomial
                    params strategy ah.2 uv.1
                  let Av := pointConditionedOutcomeOperatorAtPolynomial
                    params strategy ah.2 uv.2
                  let Moh := (M uv.1).outcome ah.1
                  opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2)
                else 0) := by
              dsimp [varianceTerm]
              rw [ev_finset_sum]
              refine Finset.sum_congr rfl ?_
              intro ah _
              by_cases hmem : ah ∈ addInUSelectionPairs params S uv.1
              · simp [hmem]
              · simp [hmem, ev_zero]
      _ ≤ ev strategy.state (∑ h : Polynomial params,
              opTensor (X h * X h) (T.outcome h)) :=
            ev_mono strategy.state _ _ (by simpa [X] using hop_le)
      _ = ev strategy.state (∑ h : Polynomial params,
              let Au := pointConditionedOutcomeOperatorAtPolynomial
                params strategy h uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial
                params strategy h uv.2
              opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h)) := by
            rw [hoperator_to_squared]
      _ = ∑ h : Polynomial params, squaredTerm uv h := by
            rw [ev_finset_sum]
  have hvariance_le_squared :
      avgOver (uniformDistribution (Point params × Point params)) varianceTerm ≤
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params, squaredTerm uv h) := by
    refine avgOver_mono _ _ _ ?_
    intro uv
    exact hpointwise uv
  have hsquared_eq :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params, squaredTerm uv h) =
      ∑ h : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T h := by
    rw [avgOver_sum]
    refine Finset.sum_congr rfl ?_
    intro h _
    unfold globalVarianceDeviationAtPolynomial
    rw [avgOver_independentPointPair_eq_uniform_prod]
    refine avgOver_congr _ _ _ ?_
    intro uv
    simp only [squaredTerm]
    rw [weightedPointConditionedOperator_sq]
  calc
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ ah : Outcome × Polynomial params,
        if ah ∈ addInUSelectionPairs params S uv.1 then
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
          let Moh := (M uv.1).outcome ah.1
          ev strategy.state
            (opTensor ((Av - Au) * Moh * (Av - Au)) (T.outcome ah.2))
        else 0)
        = avgOver (uniformDistribution (Point params × Point params)) varianceTerm := by
            rfl
    _ ≤ avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, squaredTerm uv h) := hvariance_le_squared
    _ = ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g := hsquared_eq

/-- Raw selected `Q₂ → Q₃` global-variance Cauchy--Schwarz bound after the
selected variance and self-energy factors have been estimated. -/
lemma addInU_selected_cs_chain_step3_abs_le_sqrt_globalVarianceDeviation_sum
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  by
  classical
  exact le_sqrt_of_factor_bounds_right
    (addInU_selected_cs_chain_step3_factored_cs params strategy M T S)
    (addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum
      params strategy M T S)
    (addInU_selected_cs_chain_step3_self_energy_factor_le_one params strategy M T S)

/-- Raw selected `Q₃ → Q₄` global-variance Cauchy--Schwarz bound after the
selected self-energy and variance factors have been estimated. -/
lemma addInU_selected_cs_chain_step4_abs_le_sqrt_globalVarianceDeviation_sum
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome) :
    |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  by
  classical
  exact le_sqrt_of_factor_bounds_left
    (addInU_selected_cs_chain_step4_factored_cs params strategy M T S)
    (addInU_selected_cs_chain_step4_self_energy_factor_le_one params strategy M T S)
    (addInU_selected_cs_chain_step34_variance_factor_le_globalVarianceDeviation_sum
      params strategy M T S)

/-- Upgrade the selected `Q₂ → Q₃` raw global-variance bound using an external
bound on the summed global-variance deviation. -/
lemma addInU_selected_cs_chain_step3_abs_le_sqrt_of_globalVarianceDeviation_sum_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤ Real.sqrt ζ :=
  by
  classical
  exact le_trans
    (addInU_selected_cs_chain_step3_abs_le_sqrt_globalVarianceDeviation_sum
      params strategy M T S)
    (Real.sqrt_le_sqrt hglobal)

/-- Upgrade the selected `Q₃ → Q₄` raw global-variance bound using an external
bound on the summed global-variance deviation. -/
lemma addInU_selected_cs_chain_step4_abs_le_sqrt_of_globalVarianceDeviation_sum_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤ Real.sqrt ζ :=
  by
  classical
  exact le_trans
    (addInU_selected_cs_chain_step4_abs_le_sqrt_globalVarianceDeviation_sum
      params strategy M T S)
    (Real.sqrt_le_sqrt hglobal)

/-- Combined selected Step 3/4 global-variance bridge.

The two selected replacement steps use the same summed global-variance
hypothesis.  This closed form supplies the raw selected Cauchy--Schwarz
estimates from the factored Step 3/4 proofs in this file and then applies the
external bound on the global-variance sum to both steps. -/
lemma addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤ Real.sqrt ζ ∧
      |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤ Real.sqrt ζ :=
  ⟨addInU_selected_cs_chain_step3_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy M T S hglobal,
    addInU_selected_cs_chain_step4_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy M T S hglobal⟩


/-- Self-energy factor `≤ 1` for the `Q₃ → Q₄` factored Cauchy--Schwarz.

The first square-root factor `D₁` produced by `add_in_u_cs_chain_q3_q4_factored_cs`
is bounded by `1`. The proof collapses the outer projection `A^u_{h(u)}` around
the sandwiched submeasurement `H^u_h = A^u_{h(u)} · T_h · A^u_{h(u)}` via
projectivity, then bounds the per-point sum of `opTensor (H^u_h) (T_h)` by
the submeasurement-opTensor-sum lemma, lifts to expectation via `ev ψ`,
and averages over `(u, v)` with the `v`-average collapsing to unity.

This supplies the `hD₁_le_one` hypothesis required by
`add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds`.  The proof is
fully symmetric in `u` ↔ `v` up to projection renaming, so the same
pattern directly supplies `hD₂_le_one` for the `Q₂ → Q₃` factored
`add_in_u_cs_chain_q2_q3_le_sqrt_of_factor_bounds` analogue. -/
lemma add_in_u_cs_chain_q3_q4_self_energy_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state (opTensor (Au * Mh * Au) (T.outcome h))) ≤ 1 := by
  classical
  let S : Point params → SubMeas (Polynomial params) ι :=
    fun u => sandwichedPolynomialSubMeasAt params strategy T u
  -- Projection collapse: `Au * (S u).outcome h * Au = (S u).outcome h`
  have hcollapse : ∀ (u : Point params) (h : Polynomial params),
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
      Au * (S u).outcome h * Au = (S u).outcome h := by
    intro u h Au
    have hproj : Au * Au = Au := by
      simpa [pointConditionedOutcomeOperatorAtPolynomial] using
        (strategy.pointMeasurement u).proj (h u)
    have hMh_eq : (S u).outcome h = Au * T.outcome h * Au := rfl
    rw [hMh_eq]
    exact proj_outer_sandwich_eq Au (T.outcome h) hproj
  -- Rewrite D₁ using the collapse
  have hD₁_eq :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state (opTensor (Au * Mh * Au) (T.outcome h))) =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          ev strategy.state (opTensor ((S uv.1).outcome h) (T.outcome h))) := by
    refine avgOver_congr _ _ _ ?_
    intro uv
    refine Finset.sum_congr rfl ?_
    intro h _
    dsimp
    have h_eq := hcollapse uv.1 h
    dsimp at h_eq
    rw [h_eq]
  rw [hD₁_eq]
  -- The integrand depends only on `uv.1`, so the average over `v` collapses
  rw [avgOver_uniform_fst
    (α := Point params) (β := Point params)
    (f := fun u =>
      ∑ h : Polynomial params,
        ev strategy.state (opTensor ((S u).outcome h) (T.outcome h)))]
  -- Per-point bound: the expectation sum is ≤ 1
  have hpointwise : ∀ u : Point params,
      ∑ h : Polynomial params,
        ev strategy.state (opTensor ((S u).outcome h) (T.outcome h)) ≤ 1 := by
    intro u
    have hop_sum_le_one :
        (∑ h : Polynomial params,
          opTensor ((S u).outcome h) (T.outcome h)) ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      have := SubMeas.opTensor_sum_filter_le_one (S u) T
        (fun _ : Polynomial params => True)
      simpa [Finset.filter_true] using this
    calc
      ∑ h : Polynomial params,
          ev strategy.state (opTensor ((S u).outcome h) (T.outcome h))
          = ev strategy.state
              (∑ h : Polynomial params,
                opTensor ((S u).outcome h) (T.outcome h)) := by
            rw [ev_finset_sum]
      _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) :=
            ev_mono strategy.state _ _ hop_sum_le_one
      _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized
  exact avgOver_uniform_le_of_pointwise_le _ 1 zero_le_one hpointwise

/-- Self-energy factor `≤ 1` for the `Q₂ → Q₃` factored Cauchy--Schwarz.

The second square-root factor produced by `add_in_u_cs_chain_q2_q3_factored_cs`
is bounded by `1`. For fixed `(u,v)`, the diagonal summand is one summand of the
nonnegative residual tensor sum
`Σ_{i,r,o} A^v_o H^u_i A^v_o ⊗ T_r`.  The residual sum is at most `1` by
`sandwichTensor_residual_sum_le_one`, applied to the point measurement at `v`,
the sandwiched polynomial submeasurement at `u`, and the original
submeasurement `T`. -/
lemma add_in_u_cs_chain_q2_q3_self_energy_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : Polynomial params,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state (opTensor (Av * Mh * Av) (T.outcome h))) ≤ 1 := by
  classical
  let S : Point params → SubMeas (Polynomial params) ι :=
    fun u => sandwichedPolynomialSubMeasAt params strategy T u
  have hpointwise : ∀ uv : Point params × Point params,
      (∑ h : Polynomial params,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (S uv.1).outcome h
        ev strategy.state (opTensor (Av * Mh * Av) (T.outcome h))) ≤ 1 := by
    intro uv
    let Outer : SubMeas (Fq params) ι :=
      (strategy.pointMeasurement uv.2).toSubMeas
    let Inner : SubMeas (Polynomial params) ι := S uv.1
    let Right : SubMeas (Polynomial params) ι := T
    let F : Fq params → Polynomial params → Polynomial params → Error := fun o i r =>
      ev strategy.state
        (leftTensor (ι₂ := ι)
            (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
          rightTensor (ι₁ := ι) (Right.outcome r))
    have hF_nonneg : ∀ o i r, 0 ≤ F o i r := by
      intro o i r
      exact sandwichTensorSummand_nonneg strategy.state Outer Inner Right o i r
    have hdiag_eq :
        (∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (S uv.1).outcome h
          ev strategy.state (opTensor (Av * Mh * Av) (T.outcome h))) =
        ∑ h : Polynomial params, F (h uv.2) h h := by
      refine Finset.sum_congr rfl ?_
      intro h _
      simp only [F, Outer, Inner, Right, pointConditionedOutcomeOperatorAtPolynomial]
      rw [leftTensor_mul_rightTensor_eq_opTensor]
    have hdiag_le_residual :
        (∑ h : Polynomial params, F (h uv.2) h h) ≤
          ∑ ir : Polynomial params × Polynomial params,
            ∑ o : Fq params, F o ir.1 ir.2 := by
      calc
        ∑ h : Polynomial params, F (h uv.2) h h
            ≤ ∑ h : Polynomial params, ∑ o : Fq params, F o h h := by
              refine Finset.sum_le_sum ?_
              intro h _
              exact Finset.single_le_sum
                (fun o _ => hF_nonneg o h h) (Finset.mem_univ (h uv.2))
        _ ≤ ∑ h : Polynomial params, ∑ r : Polynomial params, ∑ o : Fq params,
              F o h r := by
              refine Finset.sum_le_sum ?_
              intro h _
              exact Finset.single_le_sum
                (fun r _ => Finset.sum_nonneg fun o _ => hF_nonneg o h r)
                (Finset.mem_univ h)
        _ = ∑ ir : Polynomial params × Polynomial params,
              ∑ o : Fq params, F o ir.1 ir.2 := by
              rw [Fintype.sum_prod_type]
    calc
      (∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (S uv.1).outcome h
          ev strategy.state (opTensor (Av * Mh * Av) (T.outcome h)))
          = ∑ h : Polynomial params, F (h uv.2) h h := hdiag_eq
      _ ≤ ∑ ir : Polynomial params × Polynomial params,
            ∑ o : Fq params, F o ir.1 ir.2 := hdiag_le_residual
      _ ≤ 1 := by
            simpa [F] using
              sandwichTensor_residual_sum_le_one strategy.state strategy.isNormalized
                Outer Inner Right
  exact avgOver_uniform_le_of_pointwise_le _ 1 zero_le_one hpointwise

/-- The variance factor in the `Q₂ → Q₃` factored Cauchy--Schwarz estimate is
bounded by the polynomial sum of the global-variance deviations.

For each polynomial `h`, the sandwiched operator `H^u_h` is bounded by `1`.
Thus the summand
`(A^v_{h(v)} - A^u_{h(u)}) H^u_h (A^v_{h(v)} - A^u_{h(u)}) ⊗ T_h`
is dominated by the squared point-operator difference tensored with `T_h`.
The latter is exactly the integrand defining
`globalVarianceDeviationAtPolynomial`, after expanding the weighted
point-conditioned operator. -/
lemma add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state
          (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h))) ≤
      ∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
  classical
  let varianceTerm : Point params × Point params → Polynomial params → Error :=
    fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
      ev strategy.state
        (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h))
  let squaredTerm : Point params × Point params → Polynomial params → Error :=
    fun uv h =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state (opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h))
  have hpointwise : ∀ (h : Polynomial params) (uv : Point params × Point params),
      varianceTerm uv h ≤ squaredTerm uv h := by
    intro h uv
    set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
    set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
    have hAu_herm : Auᴴ = Au := by
      change ((strategy.pointMeasurement uv.1).toSubMeas.outcome (h uv.1))ᴴ =
        (strategy.pointMeasurement uv.1).toSubMeas.outcome (h uv.1)
      exact (strategy.pointMeasurement uv.1).toSubMeas.outcome_hermitian (h uv.1)
    have hAv_herm : Avᴴ = Av := by
      change ((strategy.pointMeasurement uv.2).toSubMeas.outcome (h uv.2))ᴴ =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome (h uv.2)
      exact (strategy.pointMeasurement uv.2).toSubMeas.outcome_hermitian (h uv.2)
    have hdiff_herm : (Av - Au)ᴴ = Av - Au := by
      rw [Matrix.conjTranspose_sub, hAv_herm, hAu_herm]
    have hleft_le :
        (Av - Au) * Mh * (Av - Au) ≤ (Av - Au) * 1 * (Av - Au) := by
      exact MIPStarRE.Quantum.sandwich_mono hdiff_herm
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_le_one h)
    have hright_eq :
        (Av - Au) * 1 * (Av - Au) = ((Au - Av)ᴴ) * (Au - Av) := by
      rw [Matrix.conjTranspose_sub, hAu_herm, hAv_herm]
      noncomm_ring
    have hop_le :
        opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h) ≤
          opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h) := by
      exact opTensor_mono_left (le_trans hleft_le (le_of_eq hright_eq)) (T.outcome_pos h)
    exact ev_mono strategy.state _ _ hop_le
  have hvariance_le_squared :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params, varianceTerm uv h) ≤
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params, squaredTerm uv h) := by
    refine avgOver_mono _ _ _ ?_
    intro uv
    exact Finset.sum_le_sum fun h _ => hpointwise h uv
  have hsquared_eq :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params, squaredTerm uv h) =
      ∑ h : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T h := by
    rw [avgOver_sum]
    refine Finset.sum_congr rfl ?_
    intro h _
    unfold globalVarianceDeviationAtPolynomial
    rw [avgOver_independentPointPair_eq_uniform_prod]
    refine avgOver_congr _ _ _ ?_
    intro uv
    simp only [squaredTerm]
    rw [weightedPointConditionedOperator_sq]
  calc
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state
          (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h)))
        = avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
            ∑ h : Polynomial params, varianceTerm uv h) := by
            refine avgOver_congr _ _ _ ?_
            intro uv
            refine Finset.sum_congr rfl ?_
            intro h _
            rfl
    _ ≤ avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, squaredTerm uv h) := hvariance_le_squared
    _ = ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g := hsquared_eq

/-- The variance factor in the `Q₃ → Q₄` factored Cauchy--Schwarz estimate is
bounded by the polynomial sum of the global-variance deviations.

This is the same variance expression as in the `Q₂ → Q₃` estimate, appearing
as the second square-root factor rather than the first. -/
lemma add_in_u_cs_chain_q3_q4_variance_factor_le_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ h : Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
        let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
        ev strategy.state
          (opTensor ((Av - Au) * Mh * (Av - Au)) (T.outcome h))) ≤
      ∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g :=
  add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum
    params strategy T

/-- Raw `Q₂ → Q₃` global-variance Cauchy--Schwarz bound after both factors have
been estimated. -/
lemma add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  add_in_u_cs_chain_q2_q3_le_sqrt_of_factor_bounds params strategy T _ _
    (add_in_u_cs_chain_q2_q3_factored_cs params strategy T)
    (add_in_u_cs_chain_q2_q3_variance_factor_le_globalVarianceDeviation_sum
      params strategy T)
    (add_in_u_cs_chain_q2_q3_self_energy_factor_le_one params strategy T)

/-- Raw `Q₃ → Q₄` global-variance Cauchy--Schwarz bound after both factors have
been estimated. -/
lemma add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds params strategy T _ _
    (add_in_u_cs_chain_q3_q4_factored_cs params strategy T)
    (add_in_u_cs_chain_q3_q4_self_energy_factor_le_one params strategy T)
    (add_in_u_cs_chain_q3_q4_variance_factor_le_globalVarianceDeviation_sum
      params strategy T)

/-- Sqrt-monotonicity transit lemma used by the two GlobalVariance endpoint
bridges below: a real bounded by `Real.sqrt s` is bounded by `Real.sqrt ζ`
whenever `s ≤ ζ`. Both `Q₂→Q₃` and `Q₃→Q₄` apply this fact with the same `s`
(the summed `globalVarianceDeviationAtPolynomial`). -/
private lemma le_sqrt_of_le_sqrt_of_le {a : ℝ} {s ζ : Error}
    (hcs : a ≤ Real.sqrt s) (hsum : s ≤ ζ) : a ≤ Real.sqrt ζ :=
  le_trans hcs (Real.sqrt_le_sqrt hsum)

/-- The global-variance sum bound upgrades the raw Cauchy--Schwarz estimate for
the first global-variance replacement step into the displayed `sqrt ζ` bound.

This is the variance-use fragment of `eq:change-one` in
`references/ldt-paper/self_improvement.tex`, lines 299--318. The hypothesis
`hcs` is the Cauchy--Schwarz estimate `eq:change-one-cauchy-schwarz`
(lines 306--311) **after** the second-square-root has been bounded by `1`
using `(A^v_{h(v)})² ≤ I` and the fact that `T` is a measurement
(lines 312--316, 318); concretely, the right-hand side is the summed
`globalVarianceDeviationAtPolynomial` (the displayed first-square-root
content). This lemma applies only the remaining `≤ ζ_variance` step from
`lem:global-variance-of-points` (line 317) via sqrt-monotonicity. -/
lemma add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (hcs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt ζ :=
  le_sqrt_of_le_sqrt_of_le hcs hglobal

/-- The global-variance sum bound upgrades the raw Cauchy--Schwarz estimate for
the second global-variance replacement step into the displayed `sqrt ζ` bound.

This is the variance-use fragment of `eq:change-another` in
`references/ldt-paper/self_improvement.tex`, lines 319--340. The hypothesis
`hcs` is the Cauchy--Schwarz estimate of lines 326--332 **after** the
first-square-root has been bounded by `1` using `(A^u_{h(u)})² ≤ I` and the
fact that `T` is a measurement (lines 333--338); concretely, the right-hand
side is the summed `globalVarianceDeviationAtPolynomial` (the displayed
second-square-root content, equal to the first-square-root term of
`eq:change-one-cauchy-schwarz` per line 340). This lemma applies only the
remaining `≤ ζ_variance` step (line 340) via sqrt-monotonicity. -/
lemma add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (hcs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt ζ :=
  le_sqrt_of_le_sqrt_of_le hcs hglobal

/-- Closed `Q₂ → Q₃` global-variance bridge using the factor estimates proved
in this file.

This is the non-conditional specialization of
`add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le`: the raw
Cauchy--Schwarz estimate is supplied by
`add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum`. -/
lemma add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt ζ :=
  add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le
    params strategy T hglobal
    (add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum params strategy T)

/-- Closed `Q₃ → Q₄` global-variance bridge using the factor estimates proved
in this file.

This is the non-conditional specialization of
`add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le`: the raw
Cauchy--Schwarz estimate is supplied by
`add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum`. -/
lemma add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt ζ :=
  add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le
    params strategy T hglobal
    (add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum params strategy T)

/-- Combined Step 3/4 variance bridge for the projection-simplified add-in-u
Cauchy--Schwarz chain.

Given the two raw Cauchy--Schwarz estimates against the summed
independent-points deviation and a GlobalVariance sum bound, this produces the
two `sqrt ζ` absolute-difference bounds needed by
`add_in_u_simplified_transfer_of_cs_chain`. It deliberately does not assemble
the final transfer, so the remaining self-consistency steps and arithmetic
absorption stay separate. -/
lemma add_in_u_cs_chain_global_variance_steps_of_sum_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (h23cs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g))
    (h34cs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt ζ ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt ζ := by
  exact
    ⟨add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le
        params strategy T hglobal h23cs,
      add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le
        params strategy T hglobal h34cs⟩

/-- Combined Step 3/4 variance bridge using the factor estimates proved in this
file.

This is the closed form of
`add_in_u_cs_chain_global_variance_steps_of_sum_bound`: the raw
Cauchy--Schwarz estimates are supplied by
`add_in_u_cs_chain_q2_q3_le_sqrt_globalVarianceDeviation_sum` and
`add_in_u_cs_chain_q3_q4_le_sqrt_globalVarianceDeviation_sum`. -/
lemma add_in_u_cs_chain_global_variance_steps_of_sum_bound_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt ζ ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt ζ :=
  ⟨add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le_from_factor_bounds
      params strategy T hglobal,
    add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le_from_factor_bounds
      params strategy T hglobal⟩

/-- Local-variance-sum version of the combined Step 3/4 variance bridge.

This consumes the expected output of the local-variance normalization step
(`expansion.tex`, lines 317--321) through
`globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le`, then applies
the combined Step 3/4 bridge above.  It remains a named bridge because the
blueprint cites this local-sum interface separately from the closed
factor-bound wrapper below. -/
lemma add_in_u_cs_chain_global_variance_steps_of_local_sum_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta)
    (h23cs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g))
    (h34cs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt (globalVarianceOfPointsError params eps delta) ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt (globalVarianceOfPointsError params eps delta) := by
  exact add_in_u_cs_chain_global_variance_steps_of_sum_bound
    params strategy T
    (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
      params strategy eps delta T hlocal)
    h23cs h34cs

/-- Closed local-variance-sum bridge for the `Q₂ → Q₃` replacement step.

The local variance theorem first gives the corresponding summed global-variance
bound; the raw Cauchy--Schwarz estimate is then supplied by the factor
estimates already proved in this file. -/
lemma add_in_u_cs_chain_q2_q3_le_sqrt_of_localVarianceDeviation_sum_le_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt (globalVarianceOfPointsError params eps delta) :=
  add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le_from_factor_bounds
    params strategy T
    (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
      params strategy eps delta T hlocal)

/-- Closed local-variance-sum bridge for the `Q₃ → Q₄` replacement step.

This is the second single-step counterpart of
`add_in_u_cs_chain_global_variance_steps_of_local_sum_bound_from_factor_bounds`.
-/
lemma add_in_u_cs_chain_q3_q4_le_sqrt_of_localVarianceDeviation_sum_le_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt (globalVarianceOfPointsError params eps delta) :=
  add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le_from_factor_bounds
    params strategy T
    (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
      params strategy eps delta T hlocal)

/-- Local-variance-sum version of the combined Step 3/4 variance bridge using
the factor estimates proved in this file.

This is the closed local-sum form of
`add_in_u_cs_chain_global_variance_steps_of_sum_bound_from_factor_bounds`: the
only new input is the local-variance sum hypothesis, which is first transported
to the global-variance sum bound. -/
lemma add_in_u_cs_chain_global_variance_steps_of_local_sum_bound_from_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) := by
  have h23 :=
    add_in_u_cs_chain_q2_q3_le_sqrt_of_localVarianceDeviation_sum_le_from_factor_bounds
      params strategy eps delta T hlocal
  have h34 :=
    add_in_u_cs_chain_q3_q4_le_sqrt_of_localVarianceDeviation_sum_le_from_factor_bounds
      params strategy eps delta T hlocal
  simpa [selfImprovementVarianceError] using And.intro h23 h34

/-- Assemble the projection-simplified scalar transfer from the four scalar
chain moves. The analytic work remains exactly the four bounds
`Q₀ ≈ Q₁`, `Q₁ ≈ Q₂`, `Q₂ ≈ Q₃`, and `Q₃ ≈ Q₄`, plus the final arithmetic
absorption into `addInUError`. -/
lemma add_in_u_simplified_transfer_of_cs_chain
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (η01 η12 η23 η34 : Error)
    (h01 :
      |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤ η01)
    (h12 :
      |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤ η12)
    (h23 :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤ η23)
    (h34 :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤ η34)
    (hsum : η01 + η12 + η23 + η34 ≤ addInUError params eps delta) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  let Q0 := addInUCSChainQ0 params strategy T
  let Q1 := addInUCSChainQ1 params strategy T
  let Q2 := addInUCSChainQ2 params strategy T
  let Q3 := addInUCSChainQ3 params strategy T
  let Q4 := addInUCSChainQ4 params strategy T
  have htriangle :
      |Q0 - Q4| ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
    calc
      |Q0 - Q4| = |(Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3) + (Q3 - Q4)| := by
        ring_nf
      _ ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
        have h1 := abs_add_le ((Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3)) (Q3 - Q4)
        have h2 := abs_add_le ((Q0 - Q1) + (Q1 - Q2)) (Q2 - Q3)
        have h3 := abs_add_le (Q0 - Q1) (Q1 - Q2)
        linarith
  calc
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))|
        = |Q0 - Q4| := by
          rw [add_in_u_cs_chain_q0_eq_match_mass,
            ← add_in_u_cs_chain_q4_eq_simplified_rhs]
    _ ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := htriangle
    _ ≤ η01 + η12 + η23 + η34 := by
      linarith
    _ ≤ addInUError params eps delta := hsum

/-- Assemble the selected add-in-`u` scalar transfer from the four selected
scalar chain moves.

This is the selection-parametrized counterpart of
`add_in_u_simplified_transfer_of_cs_chain`.  The endpoints are the theorem-side
generic add-in-u quantities rather than the diagonal match-mass and simplified
release quantities. -/
lemma add_in_u_selected_transfer_of_cs_chain
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (η01 η12 η23 η34 : Error)
    (h01 :
      |addInUSelectedCSChainQ0 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S| ≤ η01)
    (h12 :
      |addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ2 params strategy M T S| ≤ η12)
    (h23 :
      |addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ3 params strategy M T S| ≤ η23)
    (h34 :
      |addInUSelectedCSChainQ3 params strategy M T S -
        addInUSelectedCSChainQ4 params strategy M T S| ≤ η34)
    (hsum : η01 + η12 + η23 + η34 ≤ addInUError params eps delta) :
    |addInULeftQuantity params strategy M
        (averagedSandwichedPolynomialSubMeas params strategy T) S -
      addInURightQuantity params strategy M T S| ≤ addInUError params eps delta := by
  let Q0 := addInUSelectedCSChainQ0 params strategy M T S
  let Q1 := addInUSelectedCSChainQ1 params strategy M T S
  let Q2 := addInUSelectedCSChainQ2 params strategy M T S
  let Q3 := addInUSelectedCSChainQ3 params strategy M T S
  let Q4 := addInUSelectedCSChainQ4 params strategy M T S
  have htriangle :
      |Q0 - Q4| ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
    calc
      |Q0 - Q4| = |(Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3) + (Q3 - Q4)| := by
        ring_nf
      _ ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
        have h1 := abs_add_le ((Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3)) (Q3 - Q4)
        have h2 := abs_add_le ((Q0 - Q1) + (Q1 - Q2)) (Q2 - Q3)
        have h3 := abs_add_le (Q0 - Q1) (Q1 - Q2)
        linarith
  calc
    |addInULeftQuantity params strategy M
        (averagedSandwichedPolynomialSubMeas params strategy T) S -
      addInURightQuantity params strategy M T S|
        = |Q0 - Q4| := by
          rw [addInUSelectedCSChainQ0_eq_leftQuantity_averagedSandwiched,
            addInUSelectedCSChainQ4_eq_rightQuantity]
    _ ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := htriangle
    _ ≤ η01 + η12 + η23 + η34 := by
      linarith
    _ ≤ addInUError params eps delta := hsum

/-- Reusable numerical absorption: whenever `2 a ≤ b`, the four-term sum
`2 √(2 a) + 2 √b` collapses into `4 √b`. This is the schematic shape of the
paper's closing absorption step in the proof of `lem:add-in-u`
(`self_improvement.tex:341--342`). -/
lemma two_sqrt_two_mul_add_two_sqrt_le_four_sqrt
    {a b : Error} (hab : 2 * a ≤ b) :
    2 * Real.sqrt (2 * a) + 2 * Real.sqrt b ≤ 4 * Real.sqrt b := by
  have hsqrt : Real.sqrt (2 * a) ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  linarith

/-- Paper-side comparison `2 δ ≤ ζ_variance` from the closing line of the proof
of `lem:add-in-u` (`self_improvement.tex:342`,
`blueprint/src/chapter/ch07_self_improvement.tex:494`). Since
`ζ_variance = 24 m (ε + δ + m d / q)` and `m ≥ 1`, the term `24 m δ` already
exceeds `2 δ` whenever `eps, delta ≥ 0`. -/
lemma two_mul_delta_le_selfImprovementVarianceError
    (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    2 * delta ≤ selfImprovementVarianceError params eps delta := by
  have hm : (1 : Error) ≤ (params.m : Error) := by
    have hm_nat : (1 : ℕ) ≤ params.m := params.hm
    exact_mod_cast hm_nat
  have hm_nonneg : (0 : Error) ≤ (params.m : Error) := by linarith
  have hdq_nonneg : (0 : Error) ≤ ((params.d : Error) / (params.q : Error)) :=
    div_nonneg (by exact_mod_cast Nat.zero_le _) (le_of_lt params.q_cast_pos)
  rw [selfImprovementVarianceError_eq]
  calc
    2 * delta
        ≤ 24 * delta := by linarith
    _ = 24 * (1 : Error) * delta := by ring
    _ ≤ 24 * (params.m : Error) * delta := by
        have : (0 : Error) ≤ ((params.m : Error) - 1) * delta :=
          mul_nonneg (by linarith) hdelta
        nlinarith
    _ ≤ 24 * (params.m : Error) *
          (eps + delta +
            ((params.m : Error) * ((params.d : Error) / (params.q : Error)))) := by
        have h24m : (0 : Error) ≤ 24 * (params.m : Error) := by nlinarith
        have hmdq_nonneg :
            (0 : Error) ≤ (params.m : Error) *
              ((params.d : Error) / (params.q : Error)) :=
          mul_nonneg hm_nonneg hdq_nonneg
        nlinarith [mul_nonneg h24m heps, mul_nonneg h24m hmdq_nonneg]

/-- Arithmetic absorption used by `add_in_u_simplified_transfer_of_cs_chain`:
the four step-bound sum `2 √(2 δ) + 2 √(ζ_variance)` is dominated by
`addInUError = 4 ζ_variance^{1/2}` (`self_improvement.tex:341--342`,
`blueprint/src/chapter/ch07_self_improvement.tex:492--494`). This is the
arithmetic side condition that lets the step bounds with the paper-faithful
`Real.sqrt` shape (companion issues #1089 and #1090) discharge the `hsum`
hypothesis of `add_in_u_simplified_transfer_of_cs_chain`. -/
lemma two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
    (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta) :
    2 * Real.sqrt (2 * delta) +
        2 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
      addInUError params eps delta := by
  have hbase :=
    two_sqrt_two_mul_add_two_sqrt_le_four_sqrt
      (two_mul_delta_le_selfImprovementVarianceError params eps delta heps hdelta)
  simpa [addInUError, Real.sqrt_eq_rpow] using hbase

/-- Wrapper composing `add_in_u_simplified_transfer_of_cs_chain` with the
arithmetic absorption: when the four chain step bounds have the paper-faithful
shapes `√(2 δ)`, `√(2 δ)`, `√(ζ_variance)`, `√(ζ_variance)`, the
projection-simplified transfer holds with the displayed
`addInUError = 4 ζ_variance^{1/2}`. The four hypotheses match the targets of
companion issues #1089 (Step 1/2) and #1083/#1088/#1090 (Step 3/4). -/
lemma add_in_u_simplified_transfer_of_cs_chain_sqrt_form
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (Polynomial params) ι)
    (h01 :
      |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤
        Real.sqrt (2 * delta))
    (h12 :
      |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤
        Real.sqrt (2 * delta))
    (h23 :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta))
    (h34 :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta)) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  have hsum :
      Real.sqrt (2 * delta) + Real.sqrt (2 * delta) +
          Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (selfImprovementVarianceError params eps delta) ≤
        addInUError params eps delta := by
    have htwo :=
      two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
        params eps delta heps hdelta
    linarith
  exact add_in_u_simplified_transfer_of_cs_chain params strategy eps delta T
    (Real.sqrt (2 * delta)) (Real.sqrt (2 * delta))
    (Real.sqrt (selfImprovementVarianceError params eps delta))
    (Real.sqrt (selfImprovementVarianceError params eps delta))
    h01 h12 h23 h34 hsum

/-- Projection-simplified add-in-`u` transfer with the Step 3/4 variance bounds
supplied by the local-variance sum hypothesis.

After the factor estimates in this file, the remaining scalar hypotheses are
only the two self-consistency moves `Q₀ → Q₁` and `Q₁ → Q₂`, together with the
local-variance sum bound from the GlobalVariance theorem. -/
lemma add_in_u_simplified_transfer_of_cs_chain_local_variance_form
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta)
    (h01 :
      |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤
        Real.sqrt (2 * delta))
    (h12 :
      |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤
        Real.sqrt (2 * delta)) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  have hsteps :=
    add_in_u_cs_chain_global_variance_steps_of_local_sum_bound_from_factor_bounds
      params strategy eps delta T hlocal
  exact add_in_u_simplified_transfer_of_cs_chain_sqrt_form
    params strategy eps delta heps hdelta T h01 h12 hsteps.1 hsteps.2

/-- Projection-simplified add-in-`u` transfer from point self-consistency and
the local-variance sum bound.

This closes all four scalar moves in the add-in-`u` chain: Step 1 and Step 2
come from point-measurement self-consistency, while Step 3 and Step 4 are
supplied by the local-variance form above. -/
lemma add_in_u_simplified_transfer_of_cs_chain_selfConsistency_local_variance_form
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (Polynomial params) ι)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta :=
  add_in_u_simplified_transfer_of_cs_chain_local_variance_form
    params strategy eps delta heps hdelta T hlocal
    (addInU_cs_chain_step1_abs_le_sqrt_two_delta params strategy T delta hssc)
    (addInU_cs_chain_step2_abs_le_sqrt_two_delta params strategy T delta hssc)

/-- Specialization of `selfConsistencyDiagonalAddInU_of_transfer` to the
projection-simplified scalar transfer hypothesis.

Compared to `selfConsistencyDiagonalAddInU_of_transfer`, the hypothesis is
stated against the cleaner right-hand side `E_u Σ_h ⟨ψ, H^u_h ⊗ T_h ψ⟩`
obtained after collapsing the outer projection factors of
`eq:release-the-kraken` via `proj_outer_sandwich_eq`. The conclusion is
identical and can therefore feed the same diagonal helper-SSC application;
the simplification reduces the remaining Cauchy--Schwarz/global-variance
proof obligation (`self_improvement.tex:247--343`) to a transfer in the
simpler shape. -/
lemma selfConsistencyDiagonalAddInU_of_simplifiedTransfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (htransfer :
      |qBipartiteMatchMass strategy.state
          (averagedSandwichedPolynomialSubMeas params strategy T)
          (averagedSandwichedPolynomialSubMeas params strategy T) -
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                (T.outcome h)))| ≤ addInUError params eps delta) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          ev strategy.state
            (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T u).outcome h * Au)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  -- Both RHS shapes are equal to the underlying `addInURightQuantity`, so the
  -- full paper RHS (`eq:release-the-kraken`) equals the projection-collapsed
  -- RHS used in `htransfer`.
  have hRHS_eq :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          ev strategy.state
            (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T u).outcome h * Au)
              (T.outcome h)))
        = avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                (T.outcome h))) :=
    (addInURightQuantity_selfConsistencySelection_eq_release
        params strategy T).symm.trans
      (addInURightQuantity_selfConsistencySelection_eq_simplified
        params strategy T)
  rw [hRHS_eq]
  exact htransfer

private lemma sum_sum_sub_diagonal_eq_off_diagonal
    {α β : Type*} [Fintype α] [DecidableEq α] [AddCommGroup β] (F : α → α → β) :
    (∑ x : α, ∑ y : α, F x y) - (∑ x : α, F x x) =
      ∑ x : α, ∑ y ∈ (Finset.univ : Finset α).erase x, F x y := by
  classical
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ =>
    (Finset.sum_erase_eq_sub (s := Finset.univ) (a := x)
      (f := fun y => F x y) (Finset.mem_univ x)).symm

/-- Exact residual-side expansion for the helper strong self-consistency proof.

For the averaged helper `Hhat = E_u H^u` produced from the primal measurement
`T`, the difference between the helper left mass and the released diagonal
add-in-`u` right-hand side is precisely the contribution of the off-diagonal
polynomial pairs `(h',h)` with `h' ≠ h`:

`E_u \sum_h \sum_{h'≠h} ⟨ψ, H^u_{h'} ⊗ T_h ψ⟩`.

This is the exact algebraic opening of the Lean residual
`helper_left_mass - release-the-kraken`; the later Cauchy--Schwarz,
Schwartz--Zippel, point-consistency, and self-consistency estimates are the
remaining inequalities that bound this off-diagonal expression in the proof of
`item:self-improvement-self`.

This Lean identity expands the helper left mass minus the released diagonal
right-hand side directly.  It therefore differs from the paper's intermediate
``threw-in-`h'`'' expression, where the off-diagonal helper operator is still
sandwiched by `A^u_{h(u)}`. -/
theorem helper_mass_sub_release_eq_polynomial_off_diagonal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι) :
    subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas).liftLeft -
      addInURightQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
        T.toSubMeas
        (selfConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
            ev strategy.state
              (opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
                (T.toSubMeas.outcome h))) := by
  classical
  have hmass :
      subMeasMass strategy.state
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas).liftLeft =
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h' : Polynomial params,
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor
                  ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
                  (T.toSubMeas.outcome h))) := by
    have hmass0 :
        subMeasMass strategy.state
            (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas).liftLeft =
          avgOver (uniformDistribution (Point params)) (fun u =>
            ∑ h' : Polynomial params,
              ev strategy.state
                (leftTensor (ι₂ := ι)
                  (sandwichedPolynomialOutcomeOperatorAt
                    params strategy T.toSubMeas u h'))) := by
      simpa using helper_mass_eq_avg_pointwise_sandwich_sum
        params strategy T.toSubMeas
    rw [hmass0]
    refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
    intro u
    refine Finset.sum_congr rfl ?_
    intro h' _
    have hTsum :
        (∑ h : Polynomial params, T.toSubMeas.outcome h) =
          (1 : MIPStarRE.Quantum.Op ι) := by
      rw [T.toSubMeas.sum_eq_total, T.total_eq_one]
    calc
      ev strategy.state
          (leftTensor (ι₂ := ι)
            (sandwichedPolynomialOutcomeOperatorAt params strategy T.toSubMeas u h'))
          =
        ev strategy.state
          (opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
            (1 : MIPStarRE.Quantum.Op ι)) := by
          rfl
      _ =
        ev strategy.state
          (opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
            (∑ h : Polynomial params, T.toSubMeas.outcome h)) := by
          rw [hTsum]
      _ =
        ev strategy.state
          (∑ h : Polynomial params,
            opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
              (T.toSubMeas.outcome h)) := by
          rw [← opTensor_sum_right_univ]
      _ =
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
              (T.toSubMeas.outcome h)) := by
          rw [ev_sum]
  have hrelease :
      addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) =
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h)
                (T.toSubMeas.outcome h))) :=
    addInURightQuantity_selfConsistencySelection_eq_simplified
      params strategy T.toSubMeas
  rw [hmass, hrelease, ← avgOver_sub]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  have hswap :
      (∑ h' : Polynomial params,
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
                (T.toSubMeas.outcome h))) =
        ∑ h : Polynomial params,
          ∑ h' : Polynomial params,
            ev strategy.state
              (opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
                (T.toSubMeas.outcome h)) := by
    rw [Finset.sum_comm]
  rw [hswap]
  exact sum_sum_sub_diagonal_eq_off_diagonal (fun h h' =>
    ev strategy.state
      (opTensor
        ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h')
        (T.toSubMeas.outcome h)))

end MIPStarRE.LDT.SelfImprovement
