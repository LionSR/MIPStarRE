import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer

/-!
# Helper strong self-consistency obligations: core reductions

Core obligation structures, the bare off-diagonal quantity, and the two
variance-swap identities used in the helper strong self-consistency chain.

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

Paper origin: `references/ldt-paper/self_improvement.tex:255-603`
(`\label{item:self-improvement-self}` and the subsequent add-in-`u`,
self-consistency, and variance-swap chain).

**Proof obligation:** This is an internal record for the helper-stage strong
self-consistency proof, tracked by #1596.  It is not a hypothesis of a
source-labelled theorem.  Elimination: derive the fields from the
add-in-`u`, self-consistency, and global-variance estimates, and do not pass
this record across the public statement of `lem:self-improvement-helper`.

These fields isolate the remaining paper-side obligations in the proof of
`item:self-improvement-self` once the reduced helper conclusion is fixed:

1. the four scalar transport bounds along the chain
   `Q₀ \to Q₁ \to Q₂ \to Q₃ \to Q₄`, and
2. the final lower bound on the released right-hand side before the arithmetic
   absorption into `selfImprovementHelperError`.

This structure records the actual intermediate estimates still needed from the
add-in-`u`, self-consistency, and variance calculations, rather than restating
the final `BipartiteSSCRel` conclusion as an input.  It is a local proof
frontier for the helper theorem, not a hypothesis of the paper-aligned helper
theorem; the full assembly of these obligations discharges the former #1514
gap. -/
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

-- This constructor fills the helper SSC obligation record by composing the
-- point self-consistency bounds with the local-to-global variance transfer.
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

-- The off-diagonal swap invokes the selected Step 3/4 bound and the
-- local-to-global variance transfer.
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

-- This is the analogous second off-diagonal swap with the same variance
-- transfer input.
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


end MIPStarRE.LDT.SelfImprovement
