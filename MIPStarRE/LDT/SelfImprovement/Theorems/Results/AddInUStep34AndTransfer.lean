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

/-!
# Add-in-u variance-bound conversions, factored Q₃→Q₄ CS, assembly and transfer

Variance-bound conversions for Q₂→Q₃ / Q₃→Q₄, the factored
`add_in_u_cs_chain_q3_q4_factored_cs` Cauchy–Schwarz lemma with
self-energy factor bound, the four-step chain assembly, arithmetic
absorption `2√(2δ) + 2√ζ ≤ 4√ζ`, and the projection-simplified
diagonal transfer.

## Contents

- **Variance-bound conversions** — `add_in_u_cs_chain_q2_q3_abs_le_sqrt_of_sq_le`,
  `_le_sqrt_of_factor_bounds`, and the Q₃→Q₄ analogues.
- **add_in_u_cs_chain_q3_q4_factored_cs** — the factored CS lemma
  `|Q₃−Q₄| ≤ √D₁ · √D₂` with `D₁` bounded by summed
  `globalVarianceDeviationAtPolynomial`.
- **add_in_u_cs_chain_q3_q4_self_energy_factor_le_one** — the
  `D₁ ≤ 1` self-energy factor for the Q₃→Q₄ factored CS path.
- **GlobalVariance endpoint bridges** —
  `_le_sqrt_of_globalVarianceDeviation_sum_le` and
  `add_in_u_cs_chain_global_variance_steps_of_sum_bound / _of_local_sum_bound`
  upgrading raw CS estimates to `√ζ` bounds.
- **add_in_u_simplified_transfer_of_cs_chain** — the four-step chain
  assembly: given four `|Qᵢ−Qⱼ| ≤ ηᵢⱼ` bounds summing to `≤ addInUError`,
  yields the projection-simplified transfer.
- **Arithmetic absorption** — `two_mul_delta_le_selfImprovementVarianceError`
  and `two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError`
  (paper lines 341–342).
- **add_in_u_simplified_transfer_of_cs_chain_sqrt_form** — wrapper
  composing the CS chain with arithmetic absorption.
- **selfConsistencyDiagonalAddInU_of_simplifiedTransfer** — specialization
  to the projection-simplified scalar transfer hypothesis.

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
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) := by
  have hsqrt_D₂ : Real.sqrt D₂ ≤ 1 := Real.sqrt_le_one.mpr hD₂_le_one
  have hsqrt_D₁ :
      Real.sqrt D₁ ≤ Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
    Real.sqrt_le_sqrt hD₁_le
  calc
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T|
        ≤ Real.sqrt D₁ * Real.sqrt D₂ := hCS
    _ ≤ Real.sqrt D₁ * 1 :=
          mul_le_mul_of_nonneg_left hsqrt_D₂ (Real.sqrt_nonneg _)
    _ = Real.sqrt D₁ := mul_one _
    _ ≤ Real.sqrt
            (∑ g : Polynomial params,
              globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
          hsqrt_D₁

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
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) := by
  have hsqrt_D₁ : Real.sqrt D₁ ≤ 1 := Real.sqrt_le_one.mpr hD₁_le_one
  have hsqrt_D₂ :
      Real.sqrt D₂ ≤ Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
    Real.sqrt_le_sqrt hD₂_le
  calc
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T|
        ≤ Real.sqrt D₁ * Real.sqrt D₂ := hCS
    _ ≤ 1 * Real.sqrt D₂ :=
          mul_le_mul_of_nonneg_right hsqrt_D₁ (Real.sqrt_nonneg _)
    _ = Real.sqrt D₂ := one_mul _
    _ ≤ Real.sqrt
            (∑ g : Polynomial params,
              globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
          hsqrt_D₂

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
  refine MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz
    (Question := Point params × Point params) (Outcome := Polynomial params)
    (uniformDistribution (Point params × Point params))
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

/-- Local-variance-sum version of the combined Step 3/4 variance bridge.

This consumes the expected output of the local-variance normalization step
(`expansion.tex`, lines 317--321) through
`globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le`, then applies
the combined Step 3/4 bridge above. -/
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
        nlinarith
  have h01' : |Q0 - Q1| ≤ η01 := by
    simpa [Q0, Q1] using h01
  have h12' : |Q1 - Q2| ≤ η12 := by
    simpa [Q1, Q2] using h12
  have h23' : |Q2 - Q3| ≤ η23 := by
    simpa [Q2, Q3] using h23
  have h34' : |Q3 - Q4| ≤ η34 := by
    simpa [Q3, Q4] using h34
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
      nlinarith
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
    (hε : 0 ≤ eps) (hδ : 0 ≤ delta) :
    2 * delta ≤ selfImprovementVarianceError params eps delta := by
  have hm : (1 : Error) ≤ (params.m : Error) := by
    have hm_nat : (1 : ℕ) ≤ params.m := params.hm
    exact_mod_cast hm_nat
  have hm_nonneg : (0 : Error) ≤ (params.m : Error) := by linarith
  have hB : 0 ≤ generalizeBError params := by
    dsimp [generalizeBError]; positivity
  unfold selfImprovementVarianceError globalVarianceOfPointsError
  calc
    2 * delta
        ≤ 24 * delta := by linarith
    _ = 24 * (1 : Error) * delta := by ring
    _ ≤ 24 * (params.m : Error) * delta := by
        have : (0 : Error) ≤ ((params.m : Error) - 1) * delta :=
          mul_nonneg (by linarith) hδ
        nlinarith
    _ ≤ 24 * (params.m : Error) * (eps + delta + generalizeBError params) := by
        have h24m : (0 : Error) ≤ 24 * (params.m : Error) := by nlinarith
        nlinarith [mul_nonneg h24m hε, mul_nonneg h24m hB]

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
    (hε : 0 ≤ eps) (hδ : 0 ≤ delta) :
    2 * Real.sqrt (2 * delta) +
        2 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
      addInUError params eps delta := by
  have hbase :=
    two_sqrt_two_mul_add_two_sqrt_le_four_sqrt
      (two_mul_delta_le_selfImprovementVarianceError params eps delta hε hδ)
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
    (hε : 0 ≤ eps) (hδ : 0 ≤ delta)
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
        params eps delta hε hδ
    linarith
  exact add_in_u_simplified_transfer_of_cs_chain params strategy eps delta T
    (Real.sqrt (2 * delta)) (Real.sqrt (2 * delta))
    (Real.sqrt (selfImprovementVarianceError params eps delta))
    (Real.sqrt (selfImprovementVarianceError params eps delta))
    h01 h12 h23 h34 hsum

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

/-- Producer-shaped inputs for the helper-stage strong self-consistency proof.

These fields isolate the remaining paper-side obligations in the proof of
`item:self-improvement-self` once the reduced helper conclusion is fixed:

1. the four scalar transport bounds along the chain
   `Q₀ \to Q₁ \to Q₂ \to Q₃ \to Q₄`, and
2. the final lower bound on the released right-hand side before the arithmetic
   absorption into `selfImprovementHelperError`.

This structure is intentionally narrower than
`HelperStrongSelfConsistencyInput`: it records the actual intermediate estimates
still needed from the add-in-`u`, self-consistency, and variance calculations,
rather than restating the final `BipartiteSSCRel` conclusion. -/
structure HelperStrongSelfConsistencyProducerInputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (Hhat : SubMeas (Polynomial params) ι)
    (eps delta : Error) : Prop where
  /-- Paper `eq:move-one`: the `Q₀ \to Q₁` transport bound. -/
  step01Bound :
    |addInUCSChainQ0 params strategy T.toSubMeas -
        addInUCSChainQ1 params strategy T.toSubMeas| ≤
      Real.sqrt (2 * delta)
  /-- Paper `eq:move-another`: the `Q₁ \to Q₂` transport bound. -/
  step12Bound :
    |addInUCSChainQ1 params strategy T.toSubMeas -
        addInUCSChainQ2 params strategy T.toSubMeas| ≤
      Real.sqrt (2 * delta)
  /-- Paper `eq:change-one`: the `Q₂ \to Q₃` variance transport bound. -/
  step23Bound :
    |addInUCSChainQ2 params strategy T.toSubMeas -
        addInUCSChainQ3 params strategy T.toSubMeas| ≤
      Real.sqrt (selfImprovementVarianceError params eps delta)
  /-- Paper `eq:change-another`: the `Q₃ \to Q₄` variance transport bound. -/
  step34Bound :
    |addInUCSChainQ3 params strategy T.toSubMeas -
        addInUCSChainQ4 params strategy T.toSubMeas| ≤
      Real.sqrt (selfImprovementVarianceError params eps delta)
  /-- The released right-hand side is within the paper's pre-absorption helper
  SSC error of the helper mass. -/
  residualLowerBound :
    subMeasMass strategy.state Hhat.liftLeft -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) ≤
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
        addInUError params eps delta

/-- Produce the helper-stage strong self-consistency conclusion from the actual
helper construction together with the named add-in-`u`/variance transports.

The theorem consumes the reduced helper output
`SelfImprovementHelperConclusion params strategy T Hhat Z eps delta` and a
producer-shaped package of the four scalar chain bounds plus the final lower
bound on the released right-hand side. It then assembles the diagonal transfer
using `add_in_u_simplified_transfer_of_cs_chain_sqrt_form`, upgrades it to the
paper's released right-hand side via
`selfConsistencyDiagonalAddInU_of_simplifiedTransfer`, and applies the closing
arithmetic absorption
`helper_strong_self_consistency_error_le_selfImprovementHelperError`.

This is the first no-`sorry` route from the actual helper construction to the
`HelperStrongSelfConsistencyInput` surface. The remaining analytic work is
therefore pushed into the producer package, rather than left as a raw
`BipartiteSSCRel` assumption. -/
theorem helper_strong_self_consistency_of_helper_conclusion
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hproducer : HelperStrongSelfConsistencyProducerInputs
      params strategy T Hhat eps delta) :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat)
      (selfImprovementHelperError params eps delta) := by
  have htransfer_simplified :
      |qBipartiteMatchMass strategy.state
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas)
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas) -
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h)
                (T.toSubMeas.outcome h)))| ≤
        addInUError params eps delta :=
    add_in_u_simplified_transfer_of_cs_chain_sqrt_form
      params strategy eps delta heps hdelta T.toSubMeas
      hproducer.step01Bound hproducer.step12Bound
      hproducer.step23Bound hproducer.step34Bound
  have htransfer_release :
      |qBipartiteMatchMass strategy.state
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas)
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas) -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params)| ≤
        addInUError params eps delta := by
    simpa [addInURightQuantity_selfConsistencySelection_eq_release] using
      selfConsistencyDiagonalAddInU_of_simplifiedTransfer
        params strategy eps delta T.toSubMeas htransfer_simplified
  have htransfer_release_hhat :
      |qBipartiteMatchMass strategy.state Hhat Hhat -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params)| ≤
        addInUError params eps delta := by
    simpa [hhelper.averagedConstruction] using htransfer_release
  have hhelperGap :
      subMeasMass strategy.state Hhat.liftLeft -
          qBipartiteMatchMass strategy.state Hhat Hhat ≤
        11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error)) := by
    have hreleaseGap :
        addInURightQuantity params strategy
            (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
            T.toSubMeas
            (selfConsistencyAddInUSelection params) -
          qBipartiteMatchMass strategy.state Hhat Hhat ≤
        addInUError params eps delta := by
      linarith [(abs_le.mp htransfer_release_hhat).1]
    linarith [hproducer.residualLowerBound, hreleaseGap]
  have hhelperGap_absorbed :
      subMeasMass strategy.state Hhat.liftLeft -
          qBipartiteMatchMass strategy.state Hhat Hhat ≤
        selfImprovementHelperError params eps delta := by
    have habsorb :=
      helper_strong_self_consistency_error_le_selfImprovementHelperError
        params eps delta heps hdelta hd_le_q
    linarith
  have hhelperErr_nonneg :
      0 ≤ selfImprovementHelperError params eps delta := by
    exact selfImprovementHelperError_nonneg params eps delta heps hdelta
  constructor
  simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily,
    qBipartiteSSCDefect, subMeasMass, SubMeas.liftLeft] using
    (max_le hhelperErr_nonneg hhelperGap_absorbed)

/-- Promote a producer of the four add-in-`u`/variance helper-SSC bounds to the
`HelperStrongSelfConsistencyInput` surface consumed by `selfImprovement`.

This theorem does not alter the `selfImprovement` statement. It narrows the
remaining hypothesis from the final `BipartiteSSCRel` conclusion to a producer
which consumes the actual helper output together with the named intermediate
transport bounds. -/
theorem helper_strong_self_consistency_input_of_producer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (hproducer :
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusion params strategy T Hhat Z eps delta →
          HelperStrongSelfConsistencyProducerInputs
            params strategy T Hhat eps delta) :
    HelperStrongSelfConsistencyInput params strategy eps delta := by
  intro T Hhat Z hhelper
  exact helper_strong_self_consistency_of_helper_conclusion
    params strategy eps delta heps hdelta hd_le_q hhelper (hproducer hhelper)


end MIPStarRE.LDT.SelfImprovement
