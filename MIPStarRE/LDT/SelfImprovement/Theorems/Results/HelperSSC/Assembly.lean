import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperSSC.PostDeleteA
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.BoundednessTransport

/-!
# Helper strong self-consistency obligations: residual assembly

Residual lower-bound reductions, scalar-chain obligation constructors, and
the final helper-stage strong self-consistency assembly theorems.

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

variable {ι : Type} [Fintype ι] [DecidableEq ι]

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

set_option maxHeartbeats 800000 in
-- This transport lower bound expands the post-delete and move-over-v scalar
-- quantities before applying the variance-transfer estimates.
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

This is the complete route from the actual helper construction and the named
scalar obligations to helper-stage strong self-consistency. The remaining
analytic work is therefore stated as named obligations, rather than left as an
unstructured `BipartiteSSCRel` assumption. -/
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

end MIPStarRE.LDT.SelfImprovement
