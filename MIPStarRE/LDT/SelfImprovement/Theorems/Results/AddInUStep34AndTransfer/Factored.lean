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
# Add-in-u Step 3/4 factored Cauchy--Schwarz bounds

Real-valued variance-bound conversions and the non-selected factored
Cauchy--Schwarz estimates for the `Q₂ → Q₃` and `Q₃ → Q₄` add-in-u moves.

## References

- `references/ldt-paper/self_improvement.tex` lines 299--340
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/


namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real square-root absorption for the `Q₂ → Q₃` add-in-u factor order. -/
lemma addInU_le_sqrt_of_factor_bounds_right
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

/-- Real square-root absorption for the `Q₃ → Q₄` add-in-u factor order. -/
lemma addInU_le_sqrt_of_factor_bounds_left
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
  addInU_le_sqrt_of_factor_bounds_right hCS hD₁_le hD₂_le_one

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
  addInU_le_sqrt_of_factor_bounds_left hCS hD₁_le_one hD₂_le

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

end MIPStarRE.LDT.SelfImprovement
