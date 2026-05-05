import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUDiagonalAndDefs
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer

/-!
# Off-diagonal add-in-u selection infrastructure for helper point consistency

This module isolates the theorem-side `add-in-u` specialization with
`Outcome = Fq params`, `M = A`, and the off-diagonal selection
`S_u = {(a, h) : h(u) ≠ a}` used in the proof of the helper-stage
`A`-consistency bound (`eq:explicit-bound-for-A-consistency`).

It does **not** prove the full point-consistency estimate. Instead, it provides
the missing theorem-side selection object, the associated selected scalar
Cauchy--Schwarz chain, and the left/right quantity identities needed by a later
transfer theorem.

The final theorem in this file also records the numerical absorption from the
natural add-in-`u` error `4 sqrt ζ_variance` to the helper-stage error
`ζ_hat`.  Thus the remaining analytic input is precisely the
selection-dependent transfer estimate, not an additional arithmetic comparison.

## References

- `references/ldt-paper/self_improvement.tex` lines 420–437
- `blueprint/src/chapter/ch07_self_improvement.tex` lines 155–179
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The off-diagonal selection used in the helper-stage `A`-consistency
application of `lem:add-in-u`.

At each point `u`, this selects exactly the pairs `(a, h)` with `h u ≠ a`,
matching the paper's choice `S_u = {(a,h) : h(u) ≠ a}` in the proof of
`eq:explicit-bound-for-A-consistency`. -/
noncomputable def pointConsistencyAddInUSelection (params : Parameters)
    [FieldModel params.q] : AddInUSelection params (Fq params) :=
  fun u => {ah | ah.2 u ≠ ah.1}

private theorem pointConsistencyAddInUSelection_pairs_sum
    (params : Parameters) [FieldModel params.q]
    (u : Point params)
    (F : Fq params → Polynomial params → Error) :
    ∑ ah ∈ addInUSelectionPairs params (pointConsistencyAddInUSelection params) u,
        F ah.1 ah.2 =
      ∑ h : Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u), F a h := by
  classical
  apply Finset.sum_finset_product_right'
    (r := addInUSelectionPairs params (pointConsistencyAddInUSelection params) u)
    (s := (Finset.univ : Finset (Polynomial params)))
    (t := fun h => (Finset.univ : Finset (Fq params)).erase (h u))
  intro p
  rcases p with ⟨a, h⟩
  unfold addInUSelectionPairs pointConsistencyAddInUSelection
  simp [Finset.mem_erase, ne_comm]

/-! ### Off-diagonal selected scalar chain -/

/-- The off-diagonal point-consistency specialization of the selected add-in-u
chain endpoint `Q₀`. -/
noncomputable def pointConsistencyAddInUCSChainQ0
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  addInUSelectedCSChainQ0 params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T
    (pointConsistencyAddInUSelection params)

/-- The off-diagonal point-consistency specialization of the selected add-in-u
chain scalar `Q₁`. -/
noncomputable def pointConsistencyAddInUCSChainQ1
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  addInUSelectedCSChainQ1 params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T
    (pointConsistencyAddInUSelection params)

/-- The off-diagonal point-consistency specialization of the selected add-in-u
chain scalar `Q₂`. -/
noncomputable def pointConsistencyAddInUCSChainQ2
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  addInUSelectedCSChainQ2 params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T
    (pointConsistencyAddInUSelection params)

/-- The off-diagonal point-consistency specialization of the selected add-in-u
chain scalar `Q₃`. -/
noncomputable def pointConsistencyAddInUCSChainQ3
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  addInUSelectedCSChainQ3 params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T
    (pointConsistencyAddInUSelection params)

/-- The off-diagonal point-consistency specialization of the selected add-in-u
chain endpoint `Q₄`. -/
noncomputable def pointConsistencyAddInUCSChainQ4
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  addInUSelectedCSChainQ4 params strategy
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    T
    (pointConsistencyAddInUSelection params)

/-- The off-diagonal selected-chain endpoint `Q₀` is the corresponding generic
add-in-u left quantity with the averaged sandwiched polynomial submeasurement. -/
theorem pointConsistencyAddInUCSChainQ0_eq_leftQuantity_averagedSandwiched
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInULeftQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (pointConsistencyAddInUSelection params) =
      pointConsistencyAddInUCSChainQ0 params strategy T := by
  simpa [pointConsistencyAddInUCSChainQ0] using
    addInUSelectedCSChainQ0_eq_leftQuantity_averagedSandwiched
      (params := params)
      (strategy := strategy)
      (M := IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (T := T)
      (S := pointConsistencyAddInUSelection params)

/-- The off-diagonal selected-chain endpoint `Q₄` is the corresponding generic
add-in-u right quantity. -/
theorem pointConsistencyAddInUCSChainQ4_eq_rightQuantity
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInURightQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        T
        (pointConsistencyAddInUSelection params) =
      pointConsistencyAddInUCSChainQ4 params strategy T := by
  simpa [pointConsistencyAddInUCSChainQ4] using
    addInUSelectedCSChainQ4_eq_rightQuantity
      (params := params)
      (strategy := strategy)
      (M := IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (T := T)
      (S := pointConsistencyAddInUSelection params)

/-- Point-consistency add-in-u transfer assembled from the four selected scalar
chain estimates.

This theorem is the off-diagonal counterpart of the diagonal chain assembly:
once the four selected Cauchy--Schwarz moves are available with total error at
most `addInUError`, it gives the theorem-side transfer hypothesis consumed by
`pointConsistencyAddInU_off_diagonal_avg_le_of_transfer`. -/
theorem pointConsistencyAddInU_transfer_of_selected_chain_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (η01 η12 η23 η34 : Error)
    (h01 :
      |pointConsistencyAddInUCSChainQ0 params strategy T -
        pointConsistencyAddInUCSChainQ1 params strategy T| ≤ η01)
    (h12 :
      |pointConsistencyAddInUCSChainQ1 params strategy T -
        pointConsistencyAddInUCSChainQ2 params strategy T| ≤ η12)
    (h23 :
      |pointConsistencyAddInUCSChainQ2 params strategy T -
        pointConsistencyAddInUCSChainQ3 params strategy T| ≤ η23)
    (h34 :
      |pointConsistencyAddInUCSChainQ3 params strategy T -
        pointConsistencyAddInUCSChainQ4 params strategy T| ≤ η34)
    (hsum : η01 + η12 + η23 + η34 ≤ addInUError params eps delta) :
    |addInULeftQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (pointConsistencyAddInUSelection params) -
      addInURightQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        T
        (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta := by
  simpa [pointConsistencyAddInUCSChainQ0, pointConsistencyAddInUCSChainQ1,
    pointConsistencyAddInUCSChainQ2, pointConsistencyAddInUCSChainQ3,
    pointConsistencyAddInUCSChainQ4] using
    add_in_u_selected_transfer_of_cs_chain
      (params := params)
      (strategy := strategy)
      (eps := eps)
      (delta := delta)
      (M := IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (T := T)
      (S := pointConsistencyAddInUSelection params)
      (η01 := η01)
      (η12 := η12)
      (η23 := η23)
      (η34 := η34)
      h01 h12 h23 h34 hsum

/-- Point-consistency add-in-u transfer with the two self-consistency moves and
the two selected global-variance moves supplied by the proved Cauchy--Schwarz
bounds.

This is the theorem-side form of the off-diagonal application of
`lem:add-in-u`: the first two selected moves use bipartite self-consistency of
the point measurement, while the last two use the global-variance sum bound for
the polynomial submeasurement `T`. -/
theorem pointConsistencyAddInU_transfer_of_selected_chain_selfConsistency_globalVariance
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (hε : 0 ≤ eps) (hδ : 0 ≤ delta)
    (T : SubMeas (Polynomial params) ι)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
          selfImprovementVarianceError params eps delta) :
    |addInULeftQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (pointConsistencyAddInUSelection params) -
      addInURightQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        T
        (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta := by
  classical
  let ηsc : Error := Real.sqrt (2 * delta)
  let ηgv : Error := Real.sqrt (selfImprovementVarianceError params eps delta)
  have h01 :
      |pointConsistencyAddInUCSChainQ0 params strategy T -
        pointConsistencyAddInUCSChainQ1 params strategy T| ≤ ηsc := by
    simpa [pointConsistencyAddInUCSChainQ0, pointConsistencyAddInUCSChainQ1, ηsc]
      using
        addInU_selected_cs_chain_step1_abs_le_sqrt_two_delta
          (params := params)
          (strategy := strategy)
          (M := IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (T := T)
          (S := pointConsistencyAddInUSelection params)
          (delta := delta)
          hssc
  have h12 :
      |pointConsistencyAddInUCSChainQ1 params strategy T -
        pointConsistencyAddInUCSChainQ2 params strategy T| ≤ ηsc := by
    simpa [pointConsistencyAddInUCSChainQ1, pointConsistencyAddInUCSChainQ2, ηsc]
      using
        addInU_selected_cs_chain_step2_abs_le_sqrt_two_delta
          (params := params)
          (strategy := strategy)
          (M := IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (T := T)
          (S := pointConsistencyAddInUSelection params)
          (delta := delta)
          hssc
  have h23 :
      |pointConsistencyAddInUCSChainQ2 params strategy T -
        pointConsistencyAddInUCSChainQ3 params strategy T| ≤ ηgv := by
    simpa [pointConsistencyAddInUCSChainQ2, pointConsistencyAddInUCSChainQ3, ηgv]
      using
        addInU_selected_cs_chain_step3_abs_le_sqrt_of_globalVarianceDeviation_sum_le
          (params := params)
          (strategy := strategy)
          (M := IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (T := T)
          (S := pointConsistencyAddInUSelection params)
          hglobal
  have h34 :
      |pointConsistencyAddInUCSChainQ3 params strategy T -
        pointConsistencyAddInUCSChainQ4 params strategy T| ≤ ηgv := by
    simpa [pointConsistencyAddInUCSChainQ3, pointConsistencyAddInUCSChainQ4, ηgv]
      using
        addInU_selected_cs_chain_step4_abs_le_sqrt_of_globalVarianceDeviation_sum_le
          (params := params)
          (strategy := strategy)
          (M := IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          (T := T)
          (S := pointConsistencyAddInUSelection params)
          hglobal
  have hsum : ηsc + ηsc + ηgv + ηgv ≤ addInUError params eps delta := by
    have h :=
      two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
        params eps delta hε hδ
    dsimp [ηsc, ηgv]
    linarith
  exact
    pointConsistencyAddInU_transfer_of_selected_chain_bounds
      (params := params)
      (strategy := strategy)
      (eps := eps)
      (delta := delta)
      (T := T)
      (η01 := ηsc)
      (η12 := ηsc)
      (η23 := ηgv)
      (η34 := ηgv)
      h01 h12 h23 h34 hsum

/-- The left side of the helper point-consistency `add-in-u` application is the
averaged off-diagonal helper-agreement mass.

This is exactly the scalar quantity on the left of
`eq:explicit-bound-for-A-consistency`, written through the generic theorem-side
`addInULeftQuantity` interface for the off-diagonal selection. -/
theorem addInULeftQuantity_pointConsistencySelection_eq_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    addInULeftQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        H
        (pointConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state
        (addInULeftOperatorAtPoint params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          H
          (pointConsistencyAddInUSelection params) u)) = _
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  unfold addInULeftOperatorAtPoint
  rw [ev_finset_sum]
  simpa [IdxProjMeas.toIdxSubMeas] using
    pointConsistencyAddInUSelection_pairs_sum params u
      (fun a h =>
        ev strategy.state
          (opTensor ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement u).outcome a)
            (H.outcome h)))

/-- The right side of the helper point-consistency `add-in-u` application is
identically zero by projectivity of the point measurement.

For every selected pair `(a, h)` with `h u ≠ a`, the inner sandwich contains the
factor `A^u_{h(u)} A^u_a = 0`, so every summand vanishes. -/
theorem addInURightQuantity_pointConsistencySelection_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInURightQuantity params strategy
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        T
        (pointConsistencyAddInUSelection params) = 0 := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state
        (addInURightOperatorAtPoint params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params) u)) = 0
  have hpoint : ∀ u : Point params,
      ev strategy.state
        (addInURightOperatorAtPoint params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params) u) = 0 := by
    intro u
    unfold addInURightOperatorAtPoint addInUSelectionPairs
    rw [ev_finset_sum]
    refine Finset.sum_eq_zero ?_
    intro ah hh
    rcases ah with ⟨a, h⟩
    have hh' : h u ≠ a := by
      have hmem : (a, h) ∈ pointConsistencyAddInUSelection params u := by
        simpa [addInUSelectionPairs] using hh
      simpa [pointConsistencyAddInUSelection] using hmem
    change ev strategy.state
        (opTensor
          (pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
            (strategy.pointMeasurement u).outcome a *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
          (T.outcome h)) = 0
    have hortho :
        pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
            (strategy.pointMeasurement u).outcome a = 0 := by
      simpa [pointConditionedOutcomeOperatorAtPolynomial] using
        ProjMeas.outcome_orthogonal (strategy.pointMeasurement u) (h u) a hh'
    have hsandwich :
        pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
            (strategy.pointMeasurement u).outcome a *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h u = 0 := by
      rw [hortho, zero_mul]
    have hzeroTensor : opTensor (0 : MIPStarRE.Quantum.Op ι) (T.outcome h) = 0 := by
      ext i j
      simp [opTensor]
    rw [hsandwich, hzeroTensor, ev_zero]
  have hzeroAvg :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ev strategy.state
          (addInURightOperatorAtPoint params strategy
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            T
            (pointConsistencyAddInUSelection params) u)) =
        avgOver (uniformDistribution (Point params)) (fun _ => 0) := by
    refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
    intro u
    exact hpoint u
  rw [hzeroAvg, avgOver_uniform_const]

/-- Any theorem-side `add-in-u` transfer bound for the off-diagonal selection
immediately bounds the averaged helper off-diagonal mass by `addInUError`.

This is the exact theorem-side wrapper needed to connect a future generic
selection-dependent transfer theorem to the helper `A`-consistency route. -/
theorem pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (H : SubMeas (Polynomial params) ι)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          H
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ h : Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome a)
              (H.outcome h))) ≤ addInUError params eps delta := by
  have h := htransfer
  rw [addInURightQuantity_pointConsistencySelection_eq_zero] at h
  rw [addInULeftQuantity_pointConsistencySelection_eq_off_diagonal_avg] at h
  simpa using (abs_le.mp h).2

/-- Helper-stage point-consistency bound from the off-diagonal `add-in-u`
transfer estimate.

The preceding theorem gives the natural bound `addInUError`, which is equal to
`4 * sqrt ζ_variance` after rewriting by `Real.sqrt_eq_rpow`.  This wrapper
applies the numerical
absorption from `self_improvement.tex`, lines 438--443, so that the resulting
off-diagonal helper mass is already bounded by the helper-stage error
`selfImprovementHelperError`.  The only remaining analytic input is the
selection-dependent `add-in-u` transfer inequality for
`pointConsistencyAddInUSelection`. -/
theorem pointConsistencyAddInU_off_diagonal_avg_le_helper_error_of_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (T : SubMeas (Polynomial params) ι)
    (H : SubMeas (Polynomial params) ι)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          H
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ h : Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome a)
              (H.outcome h))) ≤ selfImprovementHelperError params eps delta := by
  have hoffdiag :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) ≤ addInUError params eps delta :=
    pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
      params strategy eps delta T H htransfer
  have habsorb :
      addInUError params eps delta ≤ selfImprovementHelperError params eps delta := by
    simpa [addInUError, Real.sqrt_eq_rpow] using
      helper_point_consistency_error_le_selfImprovementHelperError
        params eps delta heps hdelta
  exact hoffdiag.trans habsorb

end MIPStarRE.LDT.SelfImprovement
