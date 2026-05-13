import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport

/-!
# Helper strong self-consistency obligations

This file assembles the add-in-`u` transfer estimates and the helper residual
bound into the `HelperStrongSelfConsistencyInput` interface used by the
self-improvement theorem.

The preceding module `AddInUStep34AndTransfer` contains the scalar transport
chain and the residual algebra.  This module records the remaining named
obligations separately from that calculation, so the add-in-`u` module remains
a smaller review unit.

## Contents

- **HelperStrongSelfConsistencyObligations** — the obligation surface
  for the four scalar chain estimates and the released residual estimate.
- **helper_residualLowerBound_of_offDiagonal_bound** — reduction of the
  released residual obligation to the explicit off-diagonal polynomial-pair
  bound.
- **helper_residualLowerBound_of_paper_chain_bound** — reduction from the
  paper's `7√ζ_variance + √(2δ) + md/q` residual-chain estimate to the
  obligation field.
- **helperOffDiagonalBareQuantity_le_paper_chain_of_scalar_transports** —
  assembly of the residual-chain estimate from the displayed scalar transport
  bounds.
- **helper_strong_self_consistency_obligations_of_selfConsistency_localVariance_scalarTransports**
  —
  obligation construction from the displayed scalar transport estimates.
- **helperOffDiagonalBareQuantity_le_one** — the submeasurement contraction
  bound for the bare off-diagonal polynomial-pair mass.
- **helper_strong_self_consistency_of_helper_conclusion** — assembly of the
  obligation fields into the helper-stage strong self-consistency conclusion.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Named obligations for the helper-stage strong self-consistency proof.

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
structure HelperStrongSelfConsistencyObligations
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

/-- Construct the helper-stage obligations from the remaining mathematical
inputs after the add-in-`u` chain has been closed.

The point self-consistency hypothesis supplies the two self-consistency moves
`Q₀ → Q₁` and `Q₁ → Q₂`; the local-variance sum bound supplies the two
global-variance moves `Q₂ → Q₃` and `Q₃ → Q₄`. The only additional scalar input
is the residual lower bound for the released right-hand side. -/
lemma helper_strong_self_consistency_obligations_of_selfConsistency_localVariance
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hresidual :
      subMeasMass strategy.state Hhat.liftLeft -
          addInURightQuantity params strategy
            (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
            T.toSubMeas
            (selfConsistencyAddInUSelection params) ≤
        (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
            Real.sqrt (2 * delta) +
            ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
          addInUError params eps delta) :
    HelperStrongSelfConsistencyObligations params strategy T Hhat eps delta := by
  have hsteps :=
    add_in_u_cs_chain_global_variance_steps_of_local_sum_bound_from_factor_bounds
      params strategy eps delta T.toSubMeas hlocal
  exact
    { step01Bound :=
        addInU_cs_chain_step1_abs_le_sqrt_two_delta
          params strategy T.toSubMeas delta hssc
      step12Bound :=
        addInU_cs_chain_step2_abs_le_sqrt_two_delta
          params strategy T.toSubMeas delta hssc
      step23Bound := hsteps.1
      step34Bound := hsteps.2
      residualLowerBound := hresidual }

/-- The bare off-diagonal polynomial-pair mass appearing after the released
residual is expanded.

This is the right-hand side of
`helper_mass_sub_release_eq_polynomial_off_diagonal`, stated for an arbitrary
polynomial submeasurement `T`. -/
noncomputable def helperOffDiagonalBareQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : Polynomial params,
      ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
        ev strategy.state
          (opTensor
            ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
            (T.outcome h)))

/-- The bare off-diagonal polynomial-pair mass is a contraction.

For each point `u`, the off-diagonal sum is bounded by the full double sum
`Σ_h Σ_{h'} H^u_{h'} ⊗ T_h`, which is
`(H^u.total) ⊗ T.total`.  Both factors are submeasurement totals, so the
expectation is at most `1` in the normalized strategy state. -/
theorem helperOffDiagonalBareQuantity_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    helperOffDiagonalBareQuantity params strategy T ≤ 1 := by
  classical
  have hpointwise : ∀ u : Point params,
      (∑ h : Polynomial params,
        ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
          ev strategy.state
            (opTensor
              ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h')
              (T.outcome h))) ≤ 1 := by
    intro u
    let H := sandwichedPolynomialSubMeasAt params strategy T u
    have hnonneg : ∀ h h' : Polynomial params,
        0 ≤ ev strategy.state (opTensor (H.outcome h') (T.outcome h)) := by
      intro h h'
      exact ev_nonneg_of_psd strategy.state _ <|
        opTensor_nonneg (H.outcome_pos h') (T.outcome_pos h)
    have hoffdiag_le_full :
        (∑ h : Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
            ev strategy.state (opTensor (H.outcome h') (T.outcome h))) ≤
          ∑ h : Polynomial params,
            ∑ h' : Polynomial params,
              ev strategy.state (opTensor (H.outcome h') (T.outcome h)) := by
      refine Finset.sum_le_sum ?_
      intro h _
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset h Finset.univ)
        (fun h' _ _ => hnonneg h h')
    have hfull_op :
        (∑ h : Polynomial params,
          ∑ h' : Polynomial params, opTensor (H.outcome h') (T.outcome h)) =
          opTensor H.total T.total := by
      calc
        (∑ h : Polynomial params,
          ∑ h' : Polynomial params, opTensor (H.outcome h') (T.outcome h)) =
            ∑ h : Polynomial params, opTensor H.total (T.outcome h) := by
              refine Finset.sum_congr rfl ?_
              intro h _
              rw [← H.sum_eq_total, opTensor_sum_left_univ]
        _ = opTensor H.total T.total := by
              rw [← T.sum_eq_total, opTensor_sum_right_univ]
    have hfull_le_one :
        (∑ h : Polynomial params,
            ∑ h' : Polynomial params,
              ev strategy.state (opTensor (H.outcome h') (T.outcome h))) ≤ 1 := by
      calc
        (∑ h : Polynomial params,
            ∑ h' : Polynomial params,
              ev strategy.state (opTensor (H.outcome h') (T.outcome h))) =
            ev strategy.state
              (∑ h : Polynomial params,
                ∑ h' : Polynomial params, opTensor (H.outcome h') (T.outcome h)) := by
              rw [ev_sum]
              refine Finset.sum_congr rfl ?_
              intro h _
              rw [ev_sum]
        _ = ev strategy.state (opTensor H.total T.total) := by
              rw [hfull_op]
        _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
              exact ev_mono strategy.state _ _ <|
                le_trans
                  (opTensor_le_leftTensor (SubMeas.total_nonneg H) T.total_le_one)
                  (leftTensor_le_one (ι₂ := ι) H.total_le_one)
        _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized
    exact hoffdiag_le_full.trans hfull_le_one
  simpa [helperOffDiagonalBareQuantity] using
    avgOver_uniform_le_of_pointwise_le
      _ (1 : Error) zero_le_one hpointwise

/-! ### Off-diagonal variance swaps -/

/-- The selected support for the two off-diagonal variance swaps in the helper
SSC residual estimate.

At the point `u`, it selects precisely the ordered polynomial pairs `(h', h)`
with `h' ≠ h` and `h u = h' u`, matching the indicator support in
`eq:swapped-u-for-v` and
`eq:swapped-u-for-v-this-time-it's-personal`. -/
noncomputable def helperOffDiagonalVarianceSwapSelection
    (params : Parameters) [FieldModel params.q] :
    AddInUSelection params (Polynomial params) :=
  fun u => {hh | hh.1 ≠ hh.2 ∧ hh.2 u = hh.1 u}

private theorem helperOffDiagonalVarianceSwapSelection_pairs_sum
    (params : Parameters) [FieldModel params.q]
    (u : Point params)
    (F : Polynomial params → Polynomial params → Error) :
    ∑ hh ∈ addInUSelectionPairs params
        (helperOffDiagonalVarianceSwapSelection params) u,
        F hh.1 hh.2 =
      ∑ h : Polynomial params,
        ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
          (if h u = h' u then (1 : Error) else 0) * F h' h := by
  classical
  unfold addInUSelectionPairs helperOffDiagonalVarianceSwapSelection
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro h _
  rw [← Finset.filter_ne' Finset.univ h, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro h' _
  by_cases hne : h' ≠ h
  · by_cases heq : h u = h' u
    · rw [if_pos ⟨hne, heq⟩, if_pos hne, if_pos heq, one_mul]
    · rw [if_pos hne, if_neg heq]
      simp only [Set.mem_setOf_eq, heq, and_false, if_false]
      ring
  · have hheq : h' = h := not_not.mp hne
    subst h'
    simp only [Set.mem_setOf_eq, ne_eq, not_true_eq_false, false_and, if_false]

/-- The selected-chain endpoint `Q₄` is the off-diagonal indicator quantity. -/
theorem helperOffDiagonalSelectedCSChainQ4_eq_indicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUSelectedCSChainQ4 params strategy
        (fun _ : Point params => T) T
        (helperOffDiagonalVarianceSwapSelection params) =
      helperOffDiagonalIndicatorQuantity params strategy T := by
  classical
  rw [addInUSelectedCSChainQ4, helperOffDiagonalIndicatorQuantity]
  change avgOver (uniformDistribution (Point params × Point params))
      (fun uv : Point params × Point params =>
        (fun u : Point params =>
          ∑ ah ∈ addInUSelectionPairs params
              (helperOffDiagonalVarianceSwapSelection params) u,
            let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
            ev strategy.state (opTensor (Au * T.outcome ah.1 * Au) (T.outcome ah.2))) uv.1) = _
  rw [avgOver_uniform_fst (α := Point params) (β := Point params)
    (f := fun u : Point params =>
      ∑ ah ∈ addInUSelectionPairs params
          (helperOffDiagonalVarianceSwapSelection params) u,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
        ev strategy.state (opTensor (Au * T.outcome ah.1 * Au) (T.outcome ah.2)))]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  rw [show
      (∑ ah ∈ addInUSelectionPairs params
          (helperOffDiagonalVarianceSwapSelection params) u,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 u
        ev strategy.state (opTensor (Au * T.outcome ah.1 * Au) (T.outcome ah.2))) =
      ∑ h : Polynomial params,
        ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
          (if h u = h' u then (1 : Error) else 0) *
            ev strategy.state
              (opTensor
                (pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
                  T.outcome h' * pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
                (T.outcome h)) by
    simpa using
      helperOffDiagonalVarianceSwapSelection_pairs_sum params u
        (fun h' h =>
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          ev strategy.state (opTensor (Au * T.outcome h' * Au) (T.outcome h)))]
  refine Finset.sum_congr rfl ?_
  intro h _
  refine Finset.sum_congr rfl ?_
  intro h' _
  by_cases heq : h u = h' u
  · simp [heq, sandwichedPolynomialSubMeasAt, sandwichedPolynomialOutcomeOperatorAt,
      pointConditionedOutcomeOperatorAtPolynomial]
  · simp [heq]

/-- The selected-chain scalar `Q₃` is the one-sided swapped off-diagonal
indicator quantity. -/
theorem helperOffDiagonalSelectedCSChainQ3_eq_oneSidedSwappedIndicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUSelectedCSChainQ3 params strategy
        (fun _ : Point params => T) T
        (helperOffDiagonalVarianceSwapSelection params) =
      helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T := by
  classical
  rw [addInUSelectedCSChainQ3, helperOffDiagonalOneSidedSwappedIndicatorQuantity]
  refine avgOver_congr (uniformDistribution (Point params × Point params)) _ _ ?_
  intro uv
  rw [show
      (∑ ah ∈ addInUSelectionPairs params
          (helperOffDiagonalVarianceSwapSelection params) uv.1,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        ev strategy.state (opTensor (Au * T.outcome ah.1 * Av) (T.outcome ah.2))) =
      ∑ h : Polynomial params,
        ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
          (if h uv.1 = h' uv.1 then (1 : Error) else 0) *
            ev strategy.state
              (opTensor
                (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                  T.outcome h' *
                  pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)
                (T.outcome h)) by
    simpa using
      helperOffDiagonalVarianceSwapSelection_pairs_sum params uv.1
        (fun h' h =>
          ev strategy.state
            (opTensor
              (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                T.outcome h' *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)
              (T.outcome h)))]
  refine Finset.sum_congr rfl ?_
  intro h _
  refine Finset.sum_congr rfl ?_
  intro h' _
  by_cases heq : h uv.1 = h' uv.1
  · rw [if_pos heq]
    simp only [one_mul]
    rw [← ev_conjTranspose strategy.state]
    rw [conjTranspose_opTensor, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    have hAu : (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1)ᴴ =
        pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
    have hAv : (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)ᴴ =
        pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 :=
      SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
    have hT' : (T.outcome h')ᴴ = T.outcome h' := SubMeas.outcome_hermitian T h'
    have hT : (T.outcome h)ᴴ = T.outcome h := SubMeas.outcome_hermitian T h
    rw [hAu, hAv, hT', hT]
    simp [Matrix.mul_assoc]
  · simp [heq]

/-- The selected-chain scalar `Q₂` is the fully swapped off-diagonal indicator
quantity. -/
theorem helperOffDiagonalSelectedCSChainQ2_eq_swappedIndicator
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUSelectedCSChainQ2 params strategy
        (fun _ : Point params => T) T
        (helperOffDiagonalVarianceSwapSelection params) =
      helperOffDiagonalSwappedIndicatorQuantity params strategy T := by
  classical
  rw [addInUSelectedCSChainQ2, helperOffDiagonalSwappedIndicatorQuantity]
  change avgOver (uniformDistribution (Point params × Point params))
      (fun uv : Point params × Point params =>
        (fun u v =>
          ∑ ah ∈ addInUSelectionPairs params
              (helperOffDiagonalVarianceSwapSelection params) u,
            let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 v
            ev strategy.state (opTensor (Av * T.outcome ah.1 * Av) (T.outcome ah.2)))
          uv.1 uv.2) = _
  rw [avgOver_uniform_prod (α := Point params) (β := Point params)
    (f := fun u v =>
      ∑ ah ∈ addInUSelectionPairs params
          (helperOffDiagonalVarianceSwapSelection params) u,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 v
        ev strategy.state (opTensor (Av * T.outcome ah.1 * Av) (T.outcome ah.2)))]
  rw [avgOver_comm]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro v
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ ah ∈ addInUSelectionPairs params
            (helperOffDiagonalVarianceSwapSelection params) u,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 v
          ev strategy.state (opTensor (Av * T.outcome ah.1 * Av) (T.outcome ah.2))) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ h' ∈ (Finset.univ : Finset (Polynomial params)).erase h,
            (if h u = h' u then (1 : Error) else 0) *
              ev strategy.state
                (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v *
                    T.outcome h' * pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (T.outcome h))) := by
        refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
        intro u
        simpa using
          helperOffDiagonalVarianceSwapSelection_pairs_sum params u
            (fun h' h =>
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h v
              ev strategy.state (opTensor (Av * T.outcome h' * Av) (T.outcome h)))
    _ = _ := by
        rw [avgOver_sum]
        refine Finset.sum_congr rfl ?_
        intro h _
        rw [avgOver_finset_sum]
        refine Finset.sum_congr rfl ?_
        intro h' _
        rw [avgOver_mul_const]

/-- The first off-diagonal variance swap, corresponding to
`eq:swapped-u-for-v` in the helper SSC residual chain. -/
theorem helperOffDiagonalIndicatorQuantity_abs_sub_oneSidedSwappedIndicator_le_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |helperOffDiagonalIndicatorQuantity params strategy T -
      helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) := by
  have hsteps :=
    addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy (fun _ : Point params => T) T
      (helperOffDiagonalVarianceSwapSelection params)
      (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
        params strategy eps delta T hlocal)
  simpa [helperOffDiagonalSelectedCSChainQ4_eq_indicator,
    helperOffDiagonalSelectedCSChainQ3_eq_oneSidedSwappedIndicator,
    abs_sub_comm, selfImprovementVarianceError] using hsteps.2

/-- The second off-diagonal variance swap, corresponding to
`eq:swapped-u-for-v-this-time-it's-personal` in the helper SSC residual chain. -/
theorem helperOffDiagonalOneSidedSwappedIndicator_abs_sub_swappedIndicator_le_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T -
      helperOffDiagonalSwappedIndicatorQuantity params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) := by
  have hsteps :=
    addInU_selected_cs_chain_step34_abs_le_sqrt_of_globalVarianceDeviation_sum_le
      params strategy (fun _ : Point params => T) T
      (helperOffDiagonalVarianceSwapSelection params)
      (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
        params strategy eps delta T hlocal)
  simpa [helperOffDiagonalSelectedCSChainQ3_eq_oneSidedSwappedIndicator,
    helperOffDiagonalSelectedCSChainQ2_eq_swappedIndicator,
    abs_sub_comm, selfImprovementVarianceError] using hsteps.1

/-! ### Post-`delete-an-A` transports -/

private lemma helper_pair_sandwich_operator_sum_le
    (params : Parameters) [FieldModel params.q]
    (H T : SubMeas (Polynomial params) ι)
    (X : Polynomial params → MIPStarRE.Quantum.Op ι)
    (hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h) :
    (∑ hh : Polynomial params × Polynomial params,
        opTensor (X hh.1 * H.outcome hh.2 * X hh.1) (T.outcome hh.1)) ≤
      ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := by
  classical
  calc
    (∑ hh : Polynomial params × Polynomial params,
        opTensor (X hh.1 * H.outcome hh.2 * X hh.1) (T.outcome hh.1))
        = ∑ h : Polynomial params,
            ∑ h' : Polynomial params,
              opTensor (X h * H.outcome h' * X h) (T.outcome h) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ h : Polynomial params,
          opTensor (X h * H.total * X h) (T.outcome h) := by
          refine Finset.sum_congr rfl ?_
          intro h _
          rw [← opTensor_sum_left_univ]
          congr 1
          rw [← H.sum_eq_total, Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ h : Polynomial params,
          opTensor (X h * 1 * X h) (T.outcome h) := by
          refine Finset.sum_le_sum ?_
          intro h _
          exact opTensor_mono_left
            (MIPStarRE.Quantum.sandwich_mono (hX_herm h) H.total_le_one)
            (T.outcome_pos h)
    _ = ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) := by
          simp

private lemma helper_pair_tensor_mass_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H T : SubMeas (Polynomial params) ι) :
    (∑ hh : Polynomial params × Polynomial params,
        ev strategy.state (opTensor (H.outcome hh.2) (T.outcome hh.1))) ≤ 1 := by
  classical
  have hop_eq :
      (∑ hh : Polynomial params × Polynomial params,
          opTensor (H.outcome hh.2) (T.outcome hh.1)) =
        opTensor H.total T.total := by
    calc
      (∑ hh : Polynomial params × Polynomial params,
          opTensor (H.outcome hh.2) (T.outcome hh.1))
          = ∑ h : Polynomial params,
              ∑ h' : Polynomial params, opTensor (H.outcome h') (T.outcome h) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ h : Polynomial params, opTensor H.total (T.outcome h) := by
            refine Finset.sum_congr rfl ?_
            intro h _
            rw [← H.sum_eq_total, opTensor_sum_left_univ]
      _ = opTensor H.total T.total := by
            rw [← T.sum_eq_total, opTensor_sum_right_univ]
  have hop_le_one : opTensor H.total T.total ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) :=
    le_trans
      (opTensor_le_leftTensor (SubMeas.total_nonneg H) T.total_le_one)
      (leftTensor_le_one (ι₂ := ι) H.total_le_one)
  calc
    (∑ hh : Polynomial params × Polynomial params,
        ev strategy.state (opTensor (H.outcome hh.2) (T.outcome hh.1)))
        = ev strategy.state
            (∑ hh : Polynomial params × Polynomial params,
              opTensor (H.outcome hh.2) (T.outcome hh.1)) := by
          rw [ev_finset_sum]
    _ = ev strategy.state (opTensor H.total T.total) := by
          rw [hop_eq]
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) :=
          ev_mono strategy.state _ _ hop_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state strategy.isNormalized

private lemma helperDeleteA_clone_variance_factor_le_globalVarianceDeviation_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ hh : Polynomial params × Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
        let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
        ev strategy.state (opTensor ((Au - Av) * Hh' * (Au - Av)) (T.outcome hh.1))) ≤
      ∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
  classical
  let varianceTerm : Point params × Point params → Error := fun uv =>
    ∑ hh : Polynomial params × Polynomial params,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
      let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      ev strategy.state (opTensor ((Au - Av) * Hh' * (Au - Av)) (T.outcome hh.1))
  let squaredTerm : Point params × Point params → Polynomial params → Error := fun uv h =>
    let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
    let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
    ev strategy.state (opTensor (((Au - Av)ᴴ) * (Au - Av)) (T.outcome h))
  have hpointwise : ∀ uv : Point params × Point params,
      varianceTerm uv ≤ ∑ h : Polynomial params, squaredTerm uv h := by
    intro uv
    let H := sandwichedPolynomialSubMeasAt params strategy T uv.1
    let X : Polynomial params → MIPStarRE.Quantum.Op ι := fun h =>
      pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 -
        pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
    have hX_herm : ∀ h : Polynomial params, (X h)ᴴ = X h := by
      intro h
      have hAu :
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1)ᴴ =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (h uv.1)
      have hAv :
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2)ᴴ =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2 :=
        SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (h uv.2)
      dsimp [X]
      rw [Matrix.conjTranspose_sub, hAu, hAv]
    have hop_le :
        (∑ hh : Polynomial params × Polynomial params,
          opTensor (X hh.1 * H.outcome hh.2 * X hh.1) (T.outcome hh.1)) ≤
        ∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h) :=
      helper_pair_sandwich_operator_sum_le params H T X hX_herm
    calc
      varianceTerm uv =
          ev strategy.state
            (∑ hh : Polynomial params × Polynomial params,
              let Au := pointConditionedOutcomeOperatorAtPolynomial
                params strategy hh.1 uv.1
              let Av := pointConditionedOutcomeOperatorAtPolynomial
                params strategy hh.1 uv.2
              let Hh' := H.outcome hh.2
              opTensor ((Au - Av) * Hh' * (Au - Av)) (T.outcome hh.1)) := by
            dsimp [varianceTerm, H]
            rw [ev_finset_sum]
      _ ≤ ev strategy.state (∑ h : Polynomial params, opTensor (X h * X h) (T.outcome h)) := by
            exact ev_mono strategy.state _ _ (by simpa [X, H] using hop_le)
      _ = ∑ h : Polynomial params, squaredTerm uv h := by
            rw [ev_finset_sum]
            refine Finset.sum_congr rfl ?_
            intro h _
            dsimp [squaredTerm, X]
            rw [hX_herm h]
  have hvariance_le_squared :
      avgOver (uniformDistribution (Point params × Point params)) varianceTerm ≤
        avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, squaredTerm uv h) := by
    exact avgOver_mono _ _ _ hpointwise
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
      ∑ hh : Polynomial params × Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
        let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
        ev strategy.state (opTensor ((Au - Av) * Hh' * (Au - Av)) (T.outcome hh.1)))
        = avgOver (uniformDistribution (Point params × Point params)) varianceTerm := rfl
    _ ≤ avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ h : Polynomial params, squaredTerm uv h) := hvariance_le_squared
    _ = ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g := hsquared_eq

private lemma helperDeleteA_clone_mass_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
      ∑ hh : Polynomial params × Polynomial params,
        ev strategy.state
          (opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
            (T.outcome hh.1))) ≤ 1 := by
  classical
  have hpointwise : ∀ uv : Point params × Point params,
      (∑ hh : Polynomial params × Polynomial params,
        ev strategy.state
          (opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
            (T.outcome hh.1))) ≤ 1 := by
    intro uv
    exact helper_pair_tensor_mass_le_one params strategy
      (sandwichedPolynomialSubMeasAt params strategy T uv.1) T
  exact avgOver_uniform_le_of_pointwise_le _ 1 zero_le_one hpointwise

/-- Paper `eq:swap-u-for-v-attack-of-the-clones`: after `delete-an-A`, the
remaining point projector may be evaluated at an independent point at cost
`√ζ_variance`. -/
theorem helperDeleteAQuantity_abs_sub_clonedQuantity_le_sqrt
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta) :
    |helperDeleteAQuantity params strategy T -
      helperDeleteAClonedQuantity params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta) := by
  classical
  let 𝒟 := uniformDistribution (Point params × Point params)
  let t : Point params × Point params → Polynomial params × Polynomial params → Error :=
    fun uv hh =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
      let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      ev strategy.state (opTensor ((Au - Av) * Hh') (T.outcome hh.1))
  let x : Point params × Point params → Polynomial params × Polynomial params → Error :=
    fun uv hh =>
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
      let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      ev strategy.state (opTensor ((Au - Av) * Hh' * (Au - Av)) (T.outcome hh.1))
  let y : Point params × Point params → Polynomial params × Polynomial params → Error :=
    fun uv hh =>
      let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      ev strategy.state (opTensor Hh' (T.outcome hh.1))
  have hdiff_eq :
      helperDeleteAQuantity params strategy T - helperDeleteAClonedQuantity params strategy T =
        avgOver 𝒟 (fun uv => ∑ hh : Polynomial params × Polynomial params, t uv hh) := by
    have hdelete_prod :
        helperDeleteAQuantity params strategy T =
          avgOver 𝒟 (fun uv =>
            ∑ hh : Polynomial params × Polynomial params,
              let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
              let Hh' :=
                (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
              ev strategy.state (opTensor (Hh' * Au) (T.outcome hh.1))) := by
      unfold helperDeleteAQuantity
      rw [← avgOver_uniform_fst (α := Point params) (β := Point params)
        (f := fun u =>
          ∑ h : Polynomial params,
            ∑ h' : Polynomial params,
              let Ah := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
              ev strategy.state
                (opTensor (((sandwichedPolynomialSubMeasAt params strategy T u).outcome h') * Ah)
                  (T.outcome h)))]
      refine avgOver_congr 𝒟 _ _ ?_
      intro uv
      rw [Fintype.sum_prod_type]
    have hclone_prod :
        helperDeleteAClonedQuantity params strategy T =
          avgOver 𝒟 (fun uv =>
            ∑ hh : Polynomial params × Polynomial params,
              let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
              let Hh' :=
                (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
              ev strategy.state (opTensor (Hh' * Av) (T.outcome hh.1))) := by
      unfold helperDeleteAClonedQuantity
      refine avgOver_congr 𝒟 _ _ ?_
      intro uv
      rw [Fintype.sum_prod_type]
    rw [hdelete_prod, hclone_prod, ← avgOver_sub]
    refine avgOver_congr 𝒟 _ _ ?_
    intro uv
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro hh _
    set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
    set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
    set Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
    have hAu : Auᴴ = Au := by
      dsimp [Au]
      exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (hh.1 uv.1)
    have hAv : Avᴴ = Av := by
      dsimp [Av]
      exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (hh.1 uv.2)
    have hH : Hh'ᴴ = Hh' := by
      dsimp [Hh']
      exact SubMeas.outcome_hermitian (sandwichedPolynomialSubMeasAt params strategy T uv.1) hh.2
    have hT : (T.outcome hh.1)ᴴ = T.outcome hh.1 := SubMeas.outcome_hermitian T hh.1
    have hdiff_herm : (Au - Av)ᴴ = Au - Av := by
      rw [Matrix.conjTranspose_sub, hAu, hAv]
    calc
      ev strategy.state (opTensor (Hh' * Au) (T.outcome hh.1)) -
          ev strategy.state (opTensor (Hh' * Av) (T.outcome hh.1))
          = ev strategy.state (opTensor (Hh' * (Au - Av)) (T.outcome hh.1)) := by
            rw [← ev_sub, opTensor_sub_left]
            congr 1
            noncomm_ring
      _ = t uv hh := by
            dsimp [t, Au, Av, Hh']
            rw [← ev_conjTranspose strategy.state]
            rw [conjTranspose_opTensor, Matrix.conjTranspose_mul, hdiff_herm, hH, hT]
  have hcs :
      |avgOver 𝒟 (fun uv => ∑ hh : Polynomial params × Polynomial params, t uv hh)| ≤
        Real.sqrt (avgOver 𝒟 (fun uv =>
          ∑ hh : Polynomial params × Polynomial params, x uv hh)) *
        Real.sqrt (avgOver 𝒟 (fun uv =>
          ∑ hh : Polynomial params × Polynomial params, y uv hh)) := by
    refine MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz 𝒟 t x y ?_ ?_ ?_
    · intro uv hh
      set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
      set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
      set Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      have hAu : Auᴴ = Au := by
        dsimp [Au]
        exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (hh.1 uv.1)
      have hAv : Avᴴ = Av := by
        dsimp [Av]
        exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (hh.1 uv.2)
      have hdiff_herm : (Au - Av)ᴴ = Au - Av := by
        rw [Matrix.conjTranspose_sub, hAu, hAv]
      have hsandwich :=
        ev_opTensor_sandwich_abs_le_sqrt strategy.state (Au - Av) 1 Hh'
          (T.outcome hh.1)
          ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos hh.2)
          (T.outcome_pos hh.1)
      simpa [t, x, y, Au, Av, Hh', hdiff_herm] using hsandwich
    · intro uv hh
      set Au := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.1
      set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
      set Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
      have hH_pos : 0 ≤ Hh' :=
        (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos hh.2
      have hT_pos : 0 ≤ T.outcome hh.1 := T.outcome_pos hh.1
      have hAu : Auᴴ = Au := by
        dsimp [Au]
        exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.1).toSubMeas (hh.1 uv.1)
      have hAv : Avᴴ = Av := by
        dsimp [Av]
        exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (hh.1 uv.2)
      have hdiff_herm : (Au - Av)ᴴ = Au - Av := by
        rw [Matrix.conjTranspose_sub, hAu, hAv]
      have hleft_pos : 0 ≤ (Au - Av) * Hh' * (Au - Av) := by
        have := ((Matrix.nonneg_iff_posSemidef.mp hH_pos).conjTranspose_mul_mul_same
          (Au - Av)).nonneg
        rwa [hdiff_herm] at this
      exact ev_nonneg_of_psd strategy.state _ (opTensor_nonneg hleft_pos hT_pos)
    · intro uv hh
      exact ev_nonneg_of_psd strategy.state _ <|
        opTensor_nonneg
          ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos hh.2)
          (T.outcome_pos hh.1)
  have hvariance :
      avgOver 𝒟 (fun uv => ∑ hh : Polynomial params × Polynomial params, x uv hh) ≤
        ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g := by
    simpa [𝒟, x] using
      helperDeleteA_clone_variance_factor_le_globalVarianceDeviation_sum params strategy T
  have hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        selfImprovementVarianceError params eps delta := by
    simpa [selfImprovementVarianceError] using
      globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
        params strategy eps delta T hlocal
  have hmass :
      avgOver 𝒟 (fun uv => ∑ hh : Polynomial params × Polynomial params, y uv hh) ≤ 1 := by
    simpa [𝒟, y] using helperDeleteA_clone_mass_factor_le_one params strategy T
  have hbound := addInU_le_sqrt_of_factor_bounds_right hcs (le_trans hvariance hglobal) hmass
  simpa [hdiff_eq] using hbound

private lemma helper_moveOverV_C_contraction
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ hh : Polynomial params × Polynomial params,
          (if hh.1 uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1)
          else 0))ᴴ *
        (∑ hh : Polynomial params × Polynomial params,
          (if hh.1 uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1)
          else 0)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ hh : Polynomial params × Polynomial params,
      if hh.1 uv.2 = a then
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
          (T.outcome hh.1)
      else 0
  have hsum_eq : ∀ a : Fq params,
      (∑ hh : Polynomial params × Polynomial params,
        (if hh.1 uv.2 = a then
          opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
            (T.outcome hh.1)
        else 0)) = K a := by
    intro a
    rfl
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hH_herm : ∀ h : Polynomial params,
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)ᴴ =
          (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h :=
      SubMeas.outcome_hermitian (sandwichedPolynomialSubMeasAt params strategy T uv.1)
    have hT_herm : ∀ h : Polynomial params, (T.outcome h)ᴴ = T.outcome h :=
      SubMeas.outcome_hermitian T
    dsimp [K]
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl ?_
    intro hh _
    by_cases hmem : hh.1 uv.2 = a
    · simp [hmem, conjTranspose_opTensor, hH_herm hh.2, hT_herm hh.1]
    · simp [hmem]
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro hh _
    by_cases hmem : hh.1 uv.2 = a
    · simp [hmem, opTensor_nonneg
        ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome_pos hh.2)
        (T.outcome_pos hh.1)]
    · simp [hmem]
  have hK_sum_le_one : (∑ a : Fq params, K a) ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    have hsum_all :
        (∑ a : Fq params, K a) =
          ∑ hh : Polynomial params × Polynomial params,
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1) := by
      dsimp [K]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro hh _
      rw [Finset.sum_eq_single (hh.1 uv.2)]
      · simp
      · intro a _ ha
        simp [Ne.symm ha]
      · intro hmem
        exact (hmem (Finset.mem_univ _)).elim
    have hop_le_one :
        (∑ hh : Polynomial params × Polynomial params,
          opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
            (T.outcome hh.1)) ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
      let H := sandwichedPolynomialSubMeasAt params strategy T uv.1
      have hop_eq :
          (∑ hh : Polynomial params × Polynomial params,
              opTensor (H.outcome hh.2) (T.outcome hh.1)) =
            opTensor H.total T.total := by
        calc
          (∑ hh : Polynomial params × Polynomial params,
              opTensor (H.outcome hh.2) (T.outcome hh.1)) =
              ∑ h : Polynomial params,
                ∑ h' : Polynomial params, opTensor (H.outcome h') (T.outcome h) := by
                rw [Fintype.sum_prod_type]
          _ = ∑ h : Polynomial params, opTensor H.total (T.outcome h) := by
                refine Finset.sum_congr rfl ?_
                intro h _
                rw [← H.sum_eq_total, opTensor_sum_left_univ]
          _ = opTensor H.total T.total := by
                rw [← T.sum_eq_total, opTensor_sum_right_univ]
      simpa [H, hop_eq] using
        (le_trans
          (opTensor_le_leftTensor
            (SubMeas.total_nonneg (sandwichedPolynomialSubMeasAt params strategy T uv.1))
            T.total_le_one)
          (leftTensor_le_one (ι₂ := ι)
            (sandwichedPolynomialSubMeasAt params strategy T uv.1).total_le_one))
    exact hsum_all.trans_le hop_le_one
  have hK_le_one : ∀ a, K a ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    intro a
    calc
      K a ≤ ∑ b : Fq params, K b := by
        exact Finset.single_le_sum (fun b _ => hK_nonneg b) (Finset.mem_univ a)
      _ ≤ 1 := hK_sum_le_one
  have hsq_le : ∀ a, K a * K a ≤ K a := by
    intro a
    exact MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)
  calc
    ∑ a : Fq params,
        (∑ hh : Polynomial params × Polynomial params,
          (if hh.1 uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1)
          else 0))ᴴ *
        (∑ hh : Polynomial params × Polynomial params,
          (if hh.1 uv.2 = a then
            opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
              (T.outcome hh.1)
          else 0))
        = ∑ a : Fq params, K a * K a := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a, hK_herm a]
    _ ≤ ∑ a : Fq params, K a := Finset.sum_le_sum (fun a _ => hsq_le a)
    _ ≤ 1 := hK_sum_le_one

private lemma ev_opTensor_left_mul_comm_of_hermitian
    (ψ : QuantumState (ι × ι))
    (A H T : MIPStarRE.Quantum.Op ι)
    (hA : Aᴴ = A) (hH : Hᴴ = H) (hT : Tᴴ = T) :
    ev ψ (opTensor (A * H) T) = ev ψ (opTensor (H * A) T) := by
  rw [← ev_conjTranspose ψ]
  rw [conjTranspose_opTensor, Matrix.conjTranspose_mul, hA, hH, hT]

private lemma helper_leftTensor_mul_opTensor
    (A B C : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) A * opTensor B C = opTensor (A * B) C := by
  calc
    leftTensor (ι₂ := ι) A * opTensor B C =
        leftTensor (ι₂ := ι) A *
          (leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) C) := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]
    _ = (leftTensor (ι₂ := ι) A * leftTensor (ι₂ := ι) B) *
          rightTensor (ι₁ := ι) C := by
          rw [Matrix.mul_assoc]
    _ = leftTensor (ι₂ := ι) (A * B) * rightTensor (ι₁ := ι) C := by
          rw [leftTensor_mul_leftTensor]
    _ = opTensor (A * B) C := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]

private lemma helper_rightTensor_mul_opTensor
    (A B C : MIPStarRE.Quantum.Op ι) :
    rightTensor (ι₁ := ι) A * opTensor B C = opTensor B (A * C) := by
  calc
    rightTensor (ι₁ := ι) A * opTensor B C =
        rightTensor (ι₁ := ι) A *
          (leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) C) := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]
    _ = (rightTensor (ι₁ := ι) A * leftTensor (ι₂ := ι) B) *
          rightTensor (ι₁ := ι) C := by
          rw [Matrix.mul_assoc]
    _ = opTensor B A * rightTensor (ι₁ := ι) C := by
          rw [rightTensor_mul_leftTensor_eq_opTensor]
    _ = (leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) A) *
          rightTensor (ι₁ := ι) C := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]
    _ = leftTensor (ι₂ := ι) B *
          (rightTensor (ι₁ := ι) A * rightTensor (ι₁ := ι) C) := by
          rw [Matrix.mul_assoc]
    _ = leftTensor (ι₂ := ι) B * rightTensor (ι₁ := ι) (A * C) := by
          rw [rightTensor_mul_rightTensor]
    _ = opTensor B (A * C) := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]

private lemma ev_opTensor_right_mul_comm_of_hermitian
    (ψ : QuantumState (ι × ι))
    (H T A : MIPStarRE.Quantum.Op ι)
    (hH : Hᴴ = H) (hT : Tᴴ = T) (hA : Aᴴ = A) :
    ev ψ (opTensor H (A * T)) = ev ψ (opTensor H (T * A)) := by
  rw [← ev_conjTranspose ψ]
  rw [conjTranspose_opTensor, Matrix.conjTranspose_mul, hH, hT, hA]

/-- Paper `eq:move-over-v`: the cloned `delete-an-A` quantity can be moved to
the right tensor factor at cost `√(2δ)` from point self-consistency. -/
theorem helperDeleteAClonedQuantity_abs_sub_moveOverVQuantity_le_sqrt_two_delta
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |helperDeleteAClonedQuantity params strategy T -
      helperMoveOverVQuantity params strategy T| ≤
        Real.sqrt (2 * delta) := by
  classical
  let Aop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => leftTensor (ι₂ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => rightTensor (ι₁ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params →
      Polynomial params × Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a hh =>
      if hh.1 uv.2 = a then
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2)
          (T.outcome hh.1)
      else 0
  have hOutcome_herm : ∀ (v : Point params) (a : Fq params),
      ((strategy.pointMeasurement v).toSubMeas.outcome a)ᴴ =
        (strategy.pointMeasurement v).toSubMeas.outcome a := fun v a =>
    (strategy.pointMeasurement v).toSubMeas.outcome_hermitian a
  have hAop_herm : ∀ uv a, (Aop uv a)ᴴ = Aop uv a := by
    intro uv a
    change (leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ = _
    rw [leftTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hBop_herm : ∀ uv a, (Bop uv a)ᴴ = Bop uv a := by
    intro uv a
    change (rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ = _
    rw [rightTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hfun_A : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Aop uv a)ᴴ) = Aop uv := by
    intro uv
    funext a
    exact hAop_herm uv a
  have hfun_B : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Bop uv a)ᴴ) = Bop uv := by
    intro uv
    funext a
    exact hBop_herm uv a
  have hSDD := addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        qSDDCore strategy.state
          (fun a : Fq params => (Aop uv a)ᴴ)
          (fun a : Fq params => (Bop uv a)ᴴ)) ≤
        2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro uv
    rw [hfun_A uv, hfun_B uv]
    rfl
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
        (∑ hh : Polynomial params × Polynomial params, Cop uv a hh)ᴴ *
          (∑ hh : Polynomial params × Polynomial params, Cop uv a hh)) ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    intro uv
    simpa [Cop] using helper_moveOverV_C_contraction params strategy T uv
  have hcs := MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_right
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ hh : Polynomial params × Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a hh)) -
        (∑ a : Fq params, ∑ hh : Polynomial params × Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a hh)) =
      (∑ hh : Polynomial params × Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
          let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
          ev strategy.state (opTensor (Hh' * Av) (T.outcome hh.1))) -
        (∑ hh : Polynomial params × Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
          let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
          ev strategy.state (opTensor Hh' (T.outcome hh.1 * Av))) := by
    intro uv
    have hAvg : ∀ (X : Fq params → Polynomial params × Polynomial params →
          MIPStarRE.Quantum.Op (ι × ι)),
        (∀ a hh, hh.1 uv.2 ≠ a → X a hh = 0) →
        ∑ a : Fq params, ∑ hh : Polynomial params × Polynomial params,
            ev strategy.state (X a hh) =
          ∑ hh : Polynomial params × Polynomial params,
            ev strategy.state (X (hh.1 uv.2) hh) := by
      intro X hX
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro hh _
      rw [Finset.sum_eq_single (hh.1 uv.2)]
      · intro a _ ha
        rw [hX a hh (Ne.symm ha), ev_zero strategy.state]
      · intro hmem
        exact (hmem (Finset.mem_univ _)).elim
    have hAC_zero : ∀ a hh, hh.1 uv.2 ≠ a → Aop uv a * Cop uv a hh = 0 := by
      intro a hh ha
      simp [Cop, ha]
    have hBC_zero : ∀ a hh, hh.1 uv.2 ≠ a → Bop uv a * Cop uv a hh = 0 := by
      intro a hh ha
      simp [Cop, ha]
    rw [hAvg (fun a hh => Aop uv a * Cop uv a hh) hAC_zero,
      hAvg (fun a hh => Bop uv a * Cop uv a hh) hBC_zero]
    change
      (∑ hh : Polynomial params × Polynomial params,
          ev strategy.state (Aop uv (hh.1 uv.2) * Cop uv (hh.1 uv.2) hh)) -
        (∑ hh : Polynomial params × Polynomial params,
          ev strategy.state (Bop uv (hh.1 uv.2) * Cop uv (hh.1 uv.2) hh)) = _
    rw [← Finset.sum_sub_distrib
      (s := (Finset.univ : Finset (Polynomial params × Polynomial params)))
      (f := fun hh : Polynomial params × Polynomial params =>
        ev strategy.state (Aop uv (hh.1 uv.2) * Cop uv (hh.1 uv.2) hh))
      (g := fun hh : Polynomial params × Polynomial params =>
        ev strategy.state (Bop uv (hh.1 uv.2) * Cop uv (hh.1 uv.2) hh))]
    rw [← Finset.sum_sub_distrib
      (s := (Finset.univ : Finset (Polynomial params × Polynomial params)))
      (f := fun hh : Polynomial params × Polynomial params =>
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
        let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
        ev strategy.state (opTensor (Hh' * Av) (T.outcome hh.1)))
      (g := fun hh : Polynomial params × Polynomial params =>
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
        let Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
        ev strategy.state (opTensor Hh' (T.outcome hh.1 * Av)))]
    refine Finset.sum_congr rfl ?_
    intro hh _
    set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy hh.1 uv.2
    set Hh' := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome hh.2
    have hAv : Avᴴ = Av := by
      dsimp [Av]
      exact SubMeas.outcome_hermitian (strategy.pointMeasurement uv.2).toSubMeas (hh.1 uv.2)
    have hH : Hh'ᴴ = Hh' := by
      dsimp [Hh']
      exact SubMeas.outcome_hermitian (sandwichedPolynomialSubMeasAt params strategy T uv.1) hh.2
    have hT : (T.outcome hh.1)ᴴ = T.outcome hh.1 := SubMeas.outcome_hermitian T hh.1
    have hCop_at : Cop uv (hh.1 uv.2) hh = opTensor Hh' (T.outcome hh.1) := by
      simp [Cop, Hh']
    have hA_at : Aop uv (hh.1 uv.2) = leftTensor (ι₂ := ι) Av := rfl
    have hB_at : Bop uv (hh.1 uv.2) = rightTensor (ι₁ := ι) Av := rfl
    rw [hCop_at, hA_at, hB_at]
    have hleft :
        ev strategy.state (leftTensor (ι₂ := ι) Av * opTensor Hh' (T.outcome hh.1)) =
          ev strategy.state (opTensor (Hh' * Av) (T.outcome hh.1)) := by
      rw [helper_leftTensor_mul_opTensor]
      simpa using ev_opTensor_left_mul_comm_of_hermitian strategy.state Av Hh'
        (T.outcome hh.1) hAv hH hT
    have hright :
        ev strategy.state (rightTensor (ι₁ := ι) Av * opTensor Hh' (T.outcome hh.1)) =
          ev strategy.state (opTensor Hh' (T.outcome hh.1 * Av)) := by
      rw [helper_rightTensor_mul_opTensor]
      simpa using ev_opTensor_right_mul_comm_of_hermitian strategy.state Hh'
        (T.outcome hh.1) Av hH hT hAv
    rw [hleft, hright]
  have hmatch :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ a : Fq params, ∑ hh : Polynomial params × Polynomial params,
            ev strategy.state (Aop uv a * Cop uv a hh)) -
        avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
          ∑ a : Fq params, ∑ hh : Polynomial params × Polynomial params,
            ev strategy.state (Bop uv a * Cop uv a hh)) =
      helperDeleteAClonedQuantity params strategy T -
        helperMoveOverVQuantity params strategy T := by
    rw [← avgOver_sub]
    unfold helperDeleteAClonedQuantity helperMoveOverVQuantity
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro uv
    rw [hmatch_pointwise uv]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [← hmatch]
  exact hcs

/-- Reduce the residual obligation to the off-diagonal residual scalar
bound.

For the actual helper output, the equality
`Hhat = E_u A^u_{h(u)} T_h A^u_{h(u)}` identifies the left-hand side of
`HelperStrongSelfConsistencyObligations.residualLowerBound` with the
off-diagonal quantity isolated by
`helper_mass_sub_release_eq_polynomial_off_diagonal`.  Thus the remaining
analytic work may be stated as a bound on that concrete polynomial-pair sum,
rather than as a bound on the obligation field itself. -/
theorem helper_residualLowerBound_of_offDiagonal_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hoffdiag :
      helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
        (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
            Real.sqrt (2 * delta) +
            ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
          addInUError params eps delta) :
    subMeasMass strategy.state Hhat.liftLeft -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) ≤
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
        addInUError params eps delta := by
  rw [hhelper.averagedConstruction]
  rw [helper_mass_sub_release_eq_polynomial_off_diagonal]
  simpa [helperOffDiagonalBareQuantity] using hoffdiag

/-- Reduce the residual obligation to the paper-shaped residual-chain bound.

After `eq:release-the-kraken`, `eq:threw-in-h-prime`, `eq:delete-an-A`, and
`eq:move-over-v`, the paper bounds the expanded residual by
`7√ζ_variance + √(2δ) + md/q`.  Since
`addInUError = 4√ζ_variance`, this is exactly the obligation-side bound
`11√ζ_variance + √(2δ) + md/q - addInUError`. -/
theorem helper_residualLowerBound_of_paper_chain_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hoffdiag :
      helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
        7 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) :
    subMeasMass strategy.state Hhat.liftLeft -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) ≤
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
        addInUError params eps delta := by
  refine helper_residualLowerBound_of_offDiagonal_bound
    params strategy eps delta hhelper ?_
  have hrewrite :
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
        addInUError params eps delta =
      7 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error)) := by
    rw [addInUError]
    have hsqrt :
        Real.rpow (selfImprovementVarianceError params eps delta) (1 / (2 : Error)) =
          Real.sqrt (selfImprovementVarianceError params eps delta) := by
      exact (Real.sqrt_eq_rpow (selfImprovementVarianceError params eps delta)).symm
    rw [hsqrt]
    ring
  rw [hrewrite]
  exact hoffdiag

/-- Paper line `eq:move-over-v` yields a lower bound on the moved quantity in
terms of the helper mass and the explicit `A`-consistency defect.

This is the algebraic/slackness part of `self_improvement.tex:579-589`: average
over `v`, replace `T_h · E_v A^v_{h(v)}` by `T_h · Z` using complementary
slackness, collapse the `T`-sum to `Z`, compare `Z` to the averaged point
operator by dual feasibility, and then subtract the off-diagonal helper
agreement defect controlled by the point-consistency `add-in-u` transfer. -/
theorem helperMoveOverVQuantity_lower_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    subMeasMass strategy.state Hhat.liftLeft ≤
      helperMoveOverVQuantity params strategy T.toSubMeas + addInUError params eps delta := by
  let 𝒟 := uniformDistribution (Point params)
  let Hu : Point params → Polynomial params → MIPStarRE.Quantum.Op ι :=
    fun u h => (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h
  have hmul_avg :
      ∀ h : Polynomial params,
        averageOperatorOverDistribution 𝒟
            (fun v => T.toSubMeas.outcome h *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h v) =
          T.toSubMeas.outcome h * averagedPointOperator params strategy h := by
    intro h
    calc
      averageOperatorOverDistribution 𝒟
          (fun v => T.toSubMeas.outcome h *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
        = ∑ v ∈ 𝒟.support,
            𝒟.weight v •
              (T.toSubMeas.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h v) := by
            rfl
      _ = ∑ v ∈ 𝒟.support,
            T.toSubMeas.outcome h *
              (𝒟.weight v • pointConditionedOutcomeOperatorAtPolynomial params strategy h v) := by
            refine Finset.sum_congr rfl ?_
            intro v _
            rw [mul_smul_comm]
      _ = T.toSubMeas.outcome h *
            (∑ v ∈ 𝒟.support,
              𝒟.weight v • pointConditionedOutcomeOperatorAtPolynomial params strategy h v) := by
            rw [Matrix.mul_sum]
      _ = T.toSubMeas.outcome h * averagedPointOperator params strategy h := by
            rfl
  have hmove_eq :
      helperMoveOverVQuantity params strategy T.toSubMeas =
        avgOver 𝒟 (fun u =>
          ∑ h' : Polynomial params,
            ev strategy.state (opTensor (Hu u h') Z)) := by
    have hprod :=
      (avgOver_uniform_prod (α := Point params) (β := Point params)
        (fun u v =>
          ∑ h : Polynomial params,
            ∑ h' : Polynomial params,
              ev strategy.state
                (opTensor (Hu u h')
                  (T.toSubMeas.outcome h *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h v)))).symm
    rw [show helperMoveOverVQuantity params strategy T.toSubMeas =
          avgOver 𝒟 (fun u =>
            avgOver 𝒟 (fun v =>
              ∑ h : Polynomial params,
                ∑ h' : Polynomial params,
                  ev strategy.state
                    (opTensor (Hu u h')
                      (T.toSubMeas.outcome h *
                        pointConditionedOutcomeOperatorAtPolynomial params strategy h v)))) from by
          unfold helperMoveOverVQuantity
          exact hprod.symm]
    refine avgOver_congr 𝒟 _ _ ?_
    intro u
    calc
      avgOver 𝒟 (fun v =>
          ∑ h : Polynomial params,
            ∑ h' : Polynomial params,
              ev strategy.state
                (opTensor (Hu u h')
                  (T.toSubMeas.outcome h *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h v)))
        = avgOver 𝒟 (fun v =>
            ∑ h' : Polynomial params,
              ∑ h : Polynomial params,
                ev strategy.state
                  (opTensor (Hu u h')
                    (T.toSubMeas.outcome h *
                      pointConditionedOutcomeOperatorAtPolynomial params strategy h v))) := by
            refine avgOver_congr 𝒟 _ _ ?_
            intro v
            rw [Finset.sum_comm]
      _ = ∑ h' : Polynomial params,
            avgOver 𝒟 (fun v =>
              ∑ h : Polynomial params,
                ev strategy.state
                  (opTensor (Hu u h')
                    (T.toSubMeas.outcome h *
                      pointConditionedOutcomeOperatorAtPolynomial params strategy h v))) := by
            rw [avgOver_sum]
      _ = ∑ h' : Polynomial params,
            ∑ h : Polynomial params,
              avgOver 𝒟 (fun v =>
                ev strategy.state
                  (opTensor (Hu u h')
                    (T.toSubMeas.outcome h *
                      pointConditionedOutcomeOperatorAtPolynomial params strategy h v))) := by
            refine Finset.sum_congr rfl ?_
            intro h' _
            rw [avgOver_sum]
      _ = ∑ h' : Polynomial params,
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor (Hu u h')
                  (T.toSubMeas.outcome h * averagedPointOperator params strategy h)) := by
            refine Finset.sum_congr rfl ?_
            intro h' _
            refine Finset.sum_congr rfl ?_
            intro h _
            calc
              avgOver 𝒟 (fun v =>
                  ev strategy.state
                    (opTensor (Hu u h')
                      (T.toSubMeas.outcome h *
                        pointConditionedOutcomeOperatorAtPolynomial params strategy h v)))
                = ev strategy.state
                    (opTensor (Hu u h')
                      (averageOperatorOverDistribution 𝒟
                        (fun v => T.toSubMeas.outcome h *
                          pointConditionedOutcomeOperatorAtPolynomial params strategy h v))) := by
                    exact
                      (ev_opTensor_averageOperatorOverDistribution_right strategy.state 𝒟
                        (Hu u h')
                        (fun v => T.toSubMeas.outcome h *
                          pointConditionedOutcomeOperatorAtPolynomial params strategy h v)).symm
              _ = ev strategy.state
                    (opTensor (Hu u h')
                      (T.toSubMeas.outcome h * averagedPointOperator params strategy h)) := by
                    rw [hmul_avg h]
      _ = ∑ h' : Polynomial params,
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor (Hu u h') (T.toSubMeas.outcome h * Z)) := by
            refine Finset.sum_congr rfl ?_
            intro h' _
            refine Finset.sum_congr rfl ?_
            intro h _
            rw [hslack h]
      _ = ∑ h' : Polynomial params,
            ev strategy.state (opTensor (Hu u h') Z) := by
            refine Finset.sum_congr rfl ?_
            intro h' _
            rw [← ev_sum strategy.state]
            congr 1
            rw [← opTensor_sum_right_univ, ← Finset.sum_mul, T.toSubMeas.sum_eq_total,
              T.total_eq_one, Matrix.one_mul]
  have hagree_eq :
      ev strategy.state (helperAgreementAverageOperator params strategy Hhat) =
        avgOver 𝒟 (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor (Hu u h) (averagedPointOperator params strategy h))) := by
    rw [hhelper.averagedConstruction]
    calc
      ev strategy.state
          (helperAgreementAverageOperator params strategy
            (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas))
        = avgOver 𝒟 (fun v =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  ((averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas).outcome h))) :=
            helper_agreement_average_ev_eq_polynomial_sum params strategy _
      _ = avgOver 𝒟 (fun v =>
            ∑ h : Polynomial params,
              avgOver 𝒟 (fun u =>
                ev strategy.state (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (Hu u h)))) := by
            refine avgOver_congr 𝒟 _ _ ?_
            intro v
            refine Finset.sum_congr rfl ?_
            intro h _
            simpa [Hu, averagedSandwichedPolynomialSubMeas,
              sandwichedPolynomialSubMeasAt, sandwichedPolynomialOutcomeOperatorAt] using
              (ev_opTensor_averageOperatorOverDistribution_right strategy.state 𝒟
                (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T.toSubMeas u h))
      _ = avgOver 𝒟 (fun u =>
            avgOver 𝒟 (fun v =>
              ∑ h : Polynomial params,
                ev strategy.state (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (Hu u h)))) := by
            rw [show avgOver 𝒟 (fun v =>
                  ∑ h : Polynomial params,
                    avgOver 𝒟 (fun u =>
                      ev strategy.state (opTensor
                        (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                        (Hu u h)))) =
                avgOver 𝒟 (fun v =>
                  avgOver 𝒟 (fun u =>
                    ∑ h : Polynomial params,
                      ev strategy.state (opTensor
                        (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                        (Hu u h)))) by
                refine avgOver_congr 𝒟 _ _ ?_
                intro v
                rw [avgOver_sum]]
            exact avgOver_uniform_comm (fun v u =>
              ∑ h : Polynomial params,
                ev strategy.state (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (Hu u h)))
      _ = avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              avgOver 𝒟 (fun v =>
                ev strategy.state (opTensor
                  (pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                  (Hu u h)))) := by
            refine avgOver_congr 𝒟 _ _ ?_
            intro u
            rw [avgOver_sum]
      _ = avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor (averagedPointOperator params strategy h) (Hu u h))) := by
            refine avgOver_congr 𝒟 _ _ ?_
            intro u
            refine Finset.sum_congr rfl ?_
            intro h _
            exact
              (ev_opTensor_averageOperatorOverDistribution_left strategy.state 𝒟
                (fun v => pointConditionedOutcomeOperatorAtPolynomial params strategy h v)
                (Hu u h)).symm
      _ = avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor (Hu u h) (averagedPointOperator params strategy h))) := by
            refine avgOver_congr 𝒟 _ _ ?_
            intro u
            refine Finset.sum_congr rfl ?_
            intro h _
            exact ev_opTensor_swap_of_density_fixed strategy.state strategy.densityFixed _ _
  have hmove_ge :
      avgOver 𝒟 (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor (Hu u h) (averagedPointOperator params strategy h))) ≤
        helperMoveOverVQuantity params strategy T.toSubMeas := by
    rw [hmove_eq]
    refine avgOver_mono 𝒟 _ _ ?_
    intro u
    refine Finset.sum_le_sum ?_
    intro h _
    exact ev_mono strategy.state _ _ <|
      opTensor_mono_right
        ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome_pos h)
        (sub_nonneg.mp (by simpa [sdpDualSlackOperator] using hhelper.sdpWitness.dualFeasible h))
  have hoffdiag :
      avgOver 𝒟 (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a) (Hhat.outcome h))) ≤
        addInUError params eps delta :=
    pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
      params strategy eps delta T.toSubMeas Hhat htransfer
  have hdecomp :=
    helper_boundedness_slack_average_ev_eq_off_diagonal_avg params strategy Hhat
  have hmass_eq :
      subMeasMass strategy.state Hhat.liftLeft =
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) := by
    change ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) = _
    rw [strategy.permInvState.swap_ev Hhat.total]
  have htotal_eq :
      ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) =
        ev strategy.state (helperAgreementAverageOperator params strategy Hhat) +
          avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
                ev strategy.state
                  (opTensor ((strategy.pointMeasurement u).outcome a) (Hhat.outcome h))) := by
    linarith [hdecomp]
  calc
    subMeasMass strategy.state Hhat.liftLeft =
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) := hmass_eq
    _ = ev strategy.state (helperAgreementAverageOperator params strategy Hhat) +
          avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
                ev strategy.state
                  (opTensor
                    ((strategy.pointMeasurement u).outcome a)
                    (Hhat.outcome h))) := htotal_eq
    _ ≤ helperMoveOverVQuantity params strategy T.toSubMeas +
          avgOver 𝒟 (fun u =>
            ∑ h : Polynomial params,
              ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
                ev strategy.state
                  (opTensor ((strategy.pointMeasurement u).outcome a) (Hhat.outcome h))) := by
            linarith [hagree_eq, hmove_ge]
    _ ≤ helperMoveOverVQuantity params strategy T.toSubMeas + addInUError params eps delta := by
            linarith [hoffdiag]

/-- Assemble the paper's final residual-chain estimate from the displayed scalar
transport bounds.

The first two hypotheses are the two variance swaps used to pass from
`eq:added-indicator` to the Schwartz--Zippel endpoint.  The next two hypotheses
are the transports from `eq:delete-an-A` to `eq:move-over-v`.  The final
hypothesis is the lower bound on the `move-over-v` endpoint obtained after
substituting the averaged operator `Z` and using the explicit point-consistency
bound for the point measurement. -/
theorem helperOffDiagonalBareQuantity_le_paper_chain_of_scalar_transports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hclone :
      |helperDeleteAQuantity params strategy T.toSubMeas -
        helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T.toSubMeas -
        helperMoveOverVQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (2 * delta))
    (hmoveLower :
      subMeasMass strategy.state Hhat.liftLeft ≤
        helperMoveOverVQuantity params strategy T.toSubMeas +
          4 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
      7 * Real.sqrt (selfImprovementVarianceError params eps delta) +
        Real.sqrt (2 * delta) +
        ((params.m : Error) * (params.d : Error) / (params.q : Error)) := by
  let release :=
    addInURightQuantity params strategy
      (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
      T.toSubMeas
      (selfConsistencyAddInUSelection params)
  let ζsqrt := Real.sqrt (selfImprovementVarianceError params eps delta)
  let sqrtTwoDelta := Real.sqrt (2 * delta)
  let mdq := ((params.m : Error) * (params.d : Error) / (params.q : Error))
  have houter :
      helperOffDiagonalOuterSandwichQuantity params strategy T.toSubMeas ≤
        2 * ζsqrt + mdq := by
    simpa [ζsqrt, mdq] using
      helperOffDiagonalOuterSandwichQuantity_le_two_sqrt_variance_add_mdq_of_abs_transports
        params strategy eps delta T.toSubMeas hleft hright
  have hmove_to_delete :
      helperMoveOverVQuantity params strategy T.toSubMeas ≤
        helperDeleteAQuantity params strategy T.toSubMeas + ζsqrt + sqrtTwoDelta := by
    simpa [ζsqrt, sqrtTwoDelta] using
      helperMoveOverVQuantity_le_deleteA_of_abs_transports
        params strategy eps delta T.toSubMeas hclone hmove
  have hmove_to_full :
      helperMoveOverVQuantity params strategy T.toSubMeas ≤
        helperFullOuterSandwichQuantity params strategy T.toSubMeas + ζsqrt + sqrtTwoDelta := by
    simpa [helperFullOuterSandwichQuantity_eq_deleteAQuantity params strategy T.toSubMeas]
      using hmove_to_delete
  have hmove_to_release :
      helperMoveOverVQuantity params strategy T.toSubMeas ≤
        release + 3 * ζsqrt + sqrtTwoDelta + mdq := by
    have hfull_split :
        helperFullOuterSandwichQuantity params strategy T.toSubMeas =
          release + helperOffDiagonalOuterSandwichQuantity params strategy T.toSubMeas := by
      simpa [release] using
        helperFullOuterSandwichQuantity_eq_release_add_offDiagonalOuterSandwichQuantity
          params strategy T.toSubMeas
    linarith
  have hresidual :
      subMeasMass strategy.state Hhat.liftLeft - release ≤
        7 * ζsqrt + sqrtTwoDelta + mdq := by
    linarith
  rw [hhelper.averagedConstruction] at hresidual
  rw [helper_mass_sub_release_eq_polynomial_off_diagonal] at hresidual
  simpa [release, ζsqrt, sqrtTwoDelta, mdq, helperOffDiagonalBareQuantity] using hresidual

/-- Construct the helper-stage obligations from local variance and a named
off-diagonal residual estimate.

This produces the same named obligations as
`helper_strong_self_consistency_obligations_of_selfConsistency_localVariance`,
but its final input is the concrete off-diagonal polynomial-pair bound obtained
after expanding the released residual. -/
lemma helper_strong_self_consistency_obligations_of_selfConsistency_localVariance_offDiagonal
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hoffdiag :
      helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
        (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
            Real.sqrt (2 * delta) +
            ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
          addInUError params eps delta) :
    HelperStrongSelfConsistencyObligations params strategy T Hhat eps delta := by
  exact helper_strong_self_consistency_obligations_of_selfConsistency_localVariance
    params strategy eps delta hssc hlocal
    (helper_residualLowerBound_of_offDiagonal_bound
      params strategy eps delta hhelper hoffdiag)

/-- Construct the helper-stage obligations from the paper's final residual
chain estimate.

This variant lets downstream work target the paper's natural bound
`7√ζ_variance + √(2δ) + md/q` on the expanded off-diagonal residual.  The
conversion to the obligation's `11√ζ_variance + √(2δ) + md/q - addInUError`
form is performed internally. -/
lemma helper_strong_self_consistency_obligations_of_selfConsistency_localVariance_paperChain
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hoffdiag :
      helperOffDiagonalBareQuantity params strategy T.toSubMeas ≤
        7 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) :
    HelperStrongSelfConsistencyObligations params strategy T Hhat eps delta := by
  exact helper_strong_self_consistency_obligations_of_selfConsistency_localVariance
    params strategy eps delta hssc hlocal
    (helper_residualLowerBound_of_paper_chain_bound
      params strategy eps delta hhelper hoffdiag)

/-- Construct the helper-stage obligations directly from the scalar
transport estimates appearing in the paper.

Compared with
`helper_strong_self_consistency_obligations_of_selfConsistency_localVariance_paperChain`,
this version does not ask for the already assembled residual-chain estimate.
It consumes the two off-diagonal variance swaps, the two post-`delete-an-A`
transports, and the final lower bound on the `move-over-v` endpoint, then
assembles the residual estimate internally. -/
lemma helper_strong_self_consistency_obligations_of_selfConsistency_localVariance_scalarTransports
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hclone :
      |helperDeleteAQuantity params strategy T.toSubMeas -
        helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T.toSubMeas -
        helperMoveOverVQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (2 * delta))
    (hmoveLower :
      subMeasMass strategy.state Hhat.liftLeft ≤
        helperMoveOverVQuantity params strategy T.toSubMeas +
          4 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    HelperStrongSelfConsistencyObligations params strategy T Hhat eps delta := by
  exact
    helper_strong_self_consistency_obligations_of_selfConsistency_localVariance_paperChain
      params strategy eps delta hhelper hssc hlocal
      (helperOffDiagonalBareQuantity_le_paper_chain_of_scalar_transports
        params strategy eps delta hhelper hleft hright hclone hmove hmoveLower)

/-- Construct the helper-stage obligations from the paper's scalar transports and
the point-consistency add-in-`u` transfer.

This is the same residual-chain constructor as
`helper_strong_self_consistency_obligations_of_selfConsistency_localVariance_scalarTransports`,
but it discharges the two off-diagonal variance swaps from local variance and
the final `move-over-v` lower-bound input from complementary slackness, dual
feasibility, and the point-consistency transfer. It packages the paper lines
after `eq:move-over-v` together with the two post-`delete-an-A` scalar
transports. -/
lemma helper_ssc_obligations_of_scalarTransports_pointTransfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
        localVarianceOfPointsError params eps delta)
    (hclone :
      |helperDeleteAQuantity params strategy T.toSubMeas -
        helperDeleteAClonedQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta))
    (hmove :
      |helperDeleteAClonedQuantity params strategy T.toSubMeas -
        helperMoveOverVQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (2 * delta))
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hpointTransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    HelperStrongSelfConsistencyObligations params strategy T Hhat eps delta := by
  have hleft :
      |helperOffDiagonalIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta) :=
    helperOffDiagonalIndicatorQuantity_abs_sub_oneSidedSwappedIndicator_le_sqrt
      params strategy eps delta T.toSubMeas hlocal
  have hright :
      |helperOffDiagonalOneSidedSwappedIndicatorQuantity params strategy T.toSubMeas -
        helperOffDiagonalSwappedIndicatorQuantity params strategy T.toSubMeas| ≤
          Real.sqrt (selfImprovementVarianceError params eps delta) :=
    helperOffDiagonalOneSidedSwappedIndicator_abs_sub_swappedIndicator_le_sqrt
      params strategy eps delta T.toSubMeas hlocal
  have hmoveLower :
      subMeasMass strategy.state Hhat.liftLeft ≤
        helperMoveOverVQuantity params strategy T.toSubMeas +
          4 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
    have hlower :=
      helperMoveOverVQuantity_lower_of_pointConsistencyAddInU_transfer
        params strategy eps delta hhelper hslack hpointTransfer
    simpa [addInUError, Real.sqrt_eq_rpow] using hlower
  exact
    helper_strong_self_consistency_obligations_of_selfConsistency_localVariance_scalarTransports
      params strategy eps delta hhelper hssc hlocal hleft hright hclone hmove hmoveLower

/-- Produce the helper-stage strong self-consistency conclusion from the actual
helper construction together with the named add-in-`u`/variance transports.

The theorem consumes the reduced helper output
`SelfImprovementHelperConclusion params strategy T Hhat Z eps delta` and the
four named scalar chain obligations together with the final lower bound on the
released right-hand side. It then assembles the diagonal transfer
using `add_in_u_simplified_transfer_of_cs_chain_sqrt_form`, upgrades it to the
paper's released right-hand side via
`selfConsistencyDiagonalAddInU_of_simplifiedTransfer`, and applies the closing
arithmetic absorption
`helper_strong_self_consistency_error_le_selfImprovementHelperError`.

This is the first complete route from the actual helper construction to the
`HelperStrongSelfConsistencyInput` surface. The remaining analytic work is
therefore stated as named obligations, rather than left as an unstructured
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
    (hobligations : HelperStrongSelfConsistencyObligations
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
      hobligations.step01Bound hobligations.step12Bound
      hobligations.step23Bound hobligations.step34Bound
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
    linarith [hobligations.residualLowerBound, hreleaseGap]
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
    exact selfImprovementHelperError_nonneg params eps delta
  constructor
  simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily,
    qBipartiteSSCDefect, subMeasMass, SubMeas.liftLeft] using
    (max_le hhelperErr_nonneg hhelperGap_absorbed)

/-- Promote the four add-in-`u`/variance helper-SSC obligations to the
`HelperStrongSelfConsistencyInput` surface consumed by `selfImprovement`.

This theorem does not alter the `selfImprovement` statement. It narrows the
remaining hypothesis from the final `BipartiteSSCRel` conclusion to the named
intermediate transport and residual bounds for the actual helper output. -/
theorem helper_strong_self_consistency_input_of_obligations
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (hobligations :
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusion params strategy T Hhat Z eps delta →
          HelperStrongSelfConsistencyObligations
            params strategy T Hhat eps delta) :
    HelperStrongSelfConsistencyInput params strategy eps delta := by
  intro T Hhat Z hhelper
  exact helper_strong_self_consistency_of_helper_conclusion
    params strategy eps delta heps hdelta hd_le_q hhelper (hobligations hhelper)

/-- Construct the helper-stage strong self-consistency input from the point
self-consistency, local-variance, and residual estimates which remain after the
helper construction has been fixed.

This theorem composes the already formalized `Q₀ → Q₁ → Q₂ → Q₃ → Q₄` chain
with the closing helper-SSC theorem. It is the paper-facing form needed when
the self-improvement theorem is applied on a restricted slice: the caller
supplies the point self-consistency relation once, and supplies the local
variance and released-residual estimates for each helper output. -/
theorem helper_strong_self_consistency_input_of_selfConsistency_localVariance
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hlocal :
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusion params strategy T Hhat Z eps delta →
          (∑ g : Polynomial params,
            localVarianceDeviationAtPolynomial params strategy strategy.state T.toSubMeas g) ≤
            localVarianceOfPointsError params eps delta)
    (hresidual :
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusion params strategy T Hhat Z eps delta →
          subMeasMass strategy.state Hhat.liftLeft -
              addInURightQuantity params strategy
                (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
                T.toSubMeas
                (selfConsistencyAddInUSelection params) ≤
            (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
                Real.sqrt (2 * delta) +
                ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
              addInUError params eps delta) :
    HelperStrongSelfConsistencyInput params strategy eps delta := by
  refine helper_strong_self_consistency_input_of_obligations
    params strategy eps delta heps hdelta hd_le_q ?_
  intro T Hhat Z hhelper
  exact helper_strong_self_consistency_obligations_of_selfConsistency_localVariance
    params strategy eps delta hssc (hlocal hhelper) (hresidual hhelper)

end MIPStarRE.LDT.SelfImprovement
