import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer

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
- **helper_strong_self_consistency_obligations_of_selfConsistency_localVariance_scalarTransports** —
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

/-- Construct the helper-stage obligations from local variance and a
named off-diagonal residual estimate.

This is the same collection of obligations as
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

/-- Produce the helper-stage strong self-consistency conclusion from the actual
helper construction together with the named add-in-`u`/variance transports.

The theorem consumes the reduced helper output
`SelfImprovementHelperConclusion params strategy T Hhat Z eps delta` and a
obligations consisting of the four scalar chain bounds plus the final lower
bound on the released right-hand side. It then assembles the diagonal transfer
using `add_in_u_simplified_transfer_of_cs_chain_sqrt_form`, upgrades it to the
paper's released right-hand side via
`selfConsistencyDiagonalAddInU_of_simplifiedTransfer`, and applies the closing
arithmetic absorption
`helper_strong_self_consistency_error_le_selfImprovementHelperError`.

This is the first complete route from the actual helper construction to the
`HelperStrongSelfConsistencyInput` surface. The remaining analytic work is
therefore stated as named obligations, rather than left as a raw
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
with the closing helper-SSC wrapper. It is the paper-facing form needed when
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

/-- Build the full self-improvement bridge input when the helper strong
self-consistency field is supplied by named obligations.

This constructor isolates the first of the three residual Section 9 inputs in
`SelfImprovementObligations`. The helper-stage field is derived from the
actual helper output and the add-in-`u`/variance obligations, while the
orthonormalization and final-fields inputs remain explicit hypotheses. -/
def SelfImprovementObligations.ofHelperStrongSelfConsistencyObligations
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (hobligations :
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusion params strategy T Hhat Z eps delta →
          HelperStrongSelfConsistencyObligations
            params strategy T Hhat eps delta)
    (horthonormalization : OrthonormalizationInput params strategy eps delta)
    (hfinalFields : FinalFieldsInput params strategy eps delta nu) :
    SelfImprovementObligations params strategy eps delta nu where
  helperStrongSelfConsistency :=
    helper_strong_self_consistency_input_of_obligations
      params strategy eps delta heps hdelta hd_le_q hobligations
  orthonormalization := horthonormalization
  finalFields := hfinalFields

end MIPStarRE.LDT.SelfImprovement
