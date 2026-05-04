import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements

/-!
# Off-diagonal add-in-u selection infrastructure for helper point consistency

This module isolates the theorem-side `add-in-u` specialization with
`Outcome = Fq params`, `M = A`, and the off-diagonal selection
`S_u = {(a, h) : h(u) ≠ a}` used in the proof of the helper-stage
`A`-consistency bound (`eq:explicit-bound-for-A-consistency`).

It does **not** prove the full point-consistency estimate. Instead, it provides
the missing theorem-side selection object together with the left/right quantity
identities needed by a later transfer theorem.

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
      simp [pointConsistencyAddInUSelection] at hh
      exact hh
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

end MIPStarRE.LDT.SelfImprovement
