import MIPStarRE.LDT.Pasting.SwitcherooContraction.Raw
import MIPStarRE.LDT.Pasting.SwitcherooCompletion.SecondTerm
import MIPStarRE.LDT.Pasting.SwitcherooCompletion.Utilities
import MIPStarRE.LDT.Pasting.SwitcherooCompletion.FourthTermChain

/-!
# Section 12 pasting: switcheroo completion bounds

Completion and first-stage switcheroo error bounds.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma switcheroo_ev_opTensor_swap
    (ψbi : QuantumState (ι × ι))
    (hfix : swapDensity ψbi.density = ψbi.density)
    (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψbi (opTensor X Y) = ev ψbi (opTensor Y X) := by
  rw [show opTensor Y X = swapDensity (opTensor X Y) by rw [swapDensity_opTensor]]
  exact (ev_swapDensity_of_density_fixed ψbi hfix (opTensor X Y)).symm

private lemma switcherooCompletePartCenter_eq_target
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hfix : swapDensity ψbi.density = ψbi.density)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    avgOver (uniformDistribution (SliceQuestion params)) (fun y =>
      Preliminaries.middleSandwichExpectation ψbi
        (uniformDistribution (SliceQuestion params))
        (completePartProjFamily params family) (((M y).toSubMeas).total)) =
      switcherooAggregateTarget params ψbi family M := by
  calc
    avgOver (uniformDistribution (SliceQuestion params)) (fun y =>
        Preliminaries.middleSandwichExpectation ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartProjFamily params family) (((M y).toSubMeas).total))
      = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ev ψbi
            (opTensor
              (((M q.2).toSubMeas).total)
              ((completePartSubMeas params family q.1).total))) := by
          simpa using
            switcherooAggregateMGCenterComplete_eq_opTensor_avg
              (ι := ι) (params := params) (ψbi := ψbi) (family := family) (M := M)
    _ = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ev ψbi
            (opTensor
              ((completePartSubMeas params family q.1).total)
              (((M q.2).toSubMeas).total))) := by
          apply avgOver_congr
          intro q
          simpa using
            (switcheroo_ev_opTensor_swap ψbi hfix
              (((M q.2).toSubMeas).total)
              ((completePartSubMeas params family q.1).total))
    _ = switcherooAggregateTarget params ψbi family M := by
          simpa using
            (switcherooAggregateTarget_eq_opTensor_avg
              (ι := ι) (params := params) (ψbi := ψbi) (family := family) (M := M)).symm

-- After extracting the pointwise normalization helpers above, the final
-- four-term packaging proof elaborates within the default heartbeat budget.
/-- `lem:commutativity-switcheroo`. -/
lemma commutativitySwitcheroo {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (hfix : swapDensity ψbi.density = ψbi.density)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta omega chi : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta)
    (hselfM : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params M)
      (switcherooSelfConsistencyRight params M)
      omega)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    CommutativitySwitcherooStatement params ψbi family M zeta omega chi := by
  /-
  Paper reference: `lem:commutativity-switcheroo` in
  `references/ldt-paper/ld-pasting.tex`.
  This is the main aggregate-commutation step upgrading commutation with each
  `G^x_g` to commutation with the total `G^x`.

  The paper informally compares all four `qSDDOp` expansion terms to a single
  scalar center. In Lean it is cleaner to use two centers whose contributions
  cancel algebraically:

  * `G ⊗ M` for the first/third terms
  * `M ⊗ G` for the second/fourth terms

  This avoids inserting an extra symmetry assumption on `ψbi` at this stage.
  -/
  refine ⟨?_⟩
  let 𝒟x : Distribution (SliceQuestion params) :=
    uniformDistribution (SliceQuestion params)
  let firstTerm :=
    avgOver 𝒟x (fun x =>
      Preliminaries.leftSandwichExpectation ψbi 𝒟x M
        ((completePartSubMeas params family x).total))
  let secondTerm := switcherooAggregateSecondTerm params ψbi family M
  let thirdTerm := switcherooAggregateThirdTerm params ψbi family M
  let fourthTerm := switcherooAggregateFourthTerm params ψbi family M
  let centerGM := switcherooAggregateTarget params ψbi family M
  let centerMGComplete : Error :=
    avgOver 𝒟x (fun y =>
      Preliminaries.middleSandwichExpectation ψbi 𝒟x
        (completePartProjFamily params family) (((M y).toSubMeas).total))
  have hfirst : |firstTerm - centerGM| ≤ 2 * Real.sqrt omega := by
    simpa [firstTerm, centerGM, switcherooAggregateTarget_eq_middleSandwich] using
      switcheroo_first_term_close params ψbi hnorm family M omega hselfM
  have hsecond : |secondTerm - centerMGComplete| ≤ 2 * Real.sqrt zeta := by
    simpa [secondTerm, centerMGComplete, 𝒟x] using
      switcheroo_second_aggregate_term_close params ψbi hnorm family M zeta hselfG
  have hexpand := switcherooAggregate_qSDDOp_expand_avg params ψbi family M
  have hthird_eq : thirdTerm = fourthTerm := by
    simpa [thirdTerm, fourthTerm] using
      switcherooAggregateThirdTerm_eq_fourthTerm params ψbi family M
  have hcenter : centerMGComplete = centerGM := by
    simpa [centerGM, centerMGComplete] using
      switcherooCompletePartCenter_eq_target params ψbi hfix family M
  have hsecond' : |secondTerm - centerGM| ≤ 2 * Real.sqrt zeta := by
    simpa [hcenter] using hsecond
  have hfirst_eq :
      switcherooAggregateFirstTerm params ψbi family M = firstTerm := by
    simpa [firstTerm, completePartSubMeas, postprocess_total] using
      switcherooAggregateFirstTerm_eq_leftSandwich params ψbi family M
  have hstep1 :=
    switcherooAggregateFourthTerm_close_once_commuted_raw
      params ψbi hnorm family M chi hcomm
  have hstep2 :
      |switcherooAggregateOnceCommutedRaw params ψbi family M -
          switcherooAggregateMixedRaw params ψbi family M| ≤ Real.sqrt zeta := by
    exact switcherooAggregateOnceCommutedRaw_close_mixed
      params ψbi hnorm family M zeta hselfG
  have hstep3 :
      |switcherooAggregateMixedRaw params ψbi family M -
          switcherooAggregateLeftFrontRaw params ψbi family M| ≤ Real.sqrt zeta := by
    exact switcherooAggregateMixedRaw_close_leftFrontRaw
      params ψbi hnorm family M zeta hselfG
  have hstep4 :=
    switcherooAggregateLeftFrontRaw_close_firstSplitRaw
      params ψbi hnorm family M chi hcomm
  have hstep5 :
      switcherooAggregateFirstSplitRaw params ψbi family M =
        switcherooAggregateFirstTerm params ψbi family M := by
    simpa [switcherooAggregateFirstSplitRaw, mul_assoc] using
      switcherooAggregateFirstTerm_eq_split_by_g params ψbi family M
  have hstep5' :
      |switcherooAggregateFirstSplitRaw params ψbi family M -
          switcherooAggregateFirstTerm params ψbi family M| ≤ 0 := by
    rw [hstep5]
    simp
  have hfourth_first :
      |switcherooAggregateFourthTerm params ψbi family M -
          switcherooAggregateFirstTerm params ψbi family M| ≤
        2 * Real.sqrt zeta + 2 * Real.sqrt chi := by
    calc
      |switcherooAggregateFourthTerm params ψbi family M -
          switcherooAggregateFirstTerm params ψbi family M|
        ≤ |switcherooAggregateFourthTerm params ψbi family M -
              switcherooAggregateOnceCommutedRaw params ψbi family M| +
            |switcherooAggregateOnceCommutedRaw params ψbi family M -
              switcherooAggregateMixedRaw params ψbi family M| +
            |switcherooAggregateMixedRaw params ψbi family M -
              switcherooAggregateLeftFrontRaw params ψbi family M| +
            |switcherooAggregateLeftFrontRaw params ψbi family M -
              switcherooAggregateFirstSplitRaw params ψbi family M| +
            |switcherooAggregateFirstSplitRaw params ψbi family M -
              switcherooAggregateFirstTerm params ψbi family M| := by
              nlinarith [abs_sub_le
                (switcherooAggregateFourthTerm params ψbi family M)
                (switcherooAggregateOnceCommutedRaw params ψbi family M)
                (switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (switcherooAggregateOnceCommutedRaw params ψbi family M)
                  (switcherooAggregateMixedRaw params ψbi family M)
                  (switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (switcherooAggregateMixedRaw params ψbi family M)
                  (switcherooAggregateLeftFrontRaw params ψbi family M)
                  (switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (switcherooAggregateLeftFrontRaw params ψbi family M)
                  (switcherooAggregateFirstSplitRaw params ψbi family M)
                  (switcherooAggregateFirstTerm params ψbi family M)]
      _ ≤ Real.sqrt chi + Real.sqrt zeta + Real.sqrt zeta + Real.sqrt chi + 0 := by
            nlinarith [hstep1, hstep2, hstep3, hstep4, hstep5']
      _ = 2 * Real.sqrt zeta + 2 * Real.sqrt chi := by ring
  have hfourth_first' :
      |fourthTerm - firstTerm| ≤ 2 * Real.sqrt zeta + 2 * Real.sqrt chi := by
    rw [← hfirst_eq]
    simpa [fourthTerm] using hfourth_first
  have hfourth : |fourthTerm - centerGM| ≤
      2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by
    calc
      |fourthTerm - centerGM| ≤ |fourthTerm - firstTerm| + |firstTerm - centerGM| := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (abs_sub_le fourthTerm firstTerm centerGM)
      _ ≤ (2 * Real.sqrt zeta + 2 * Real.sqrt chi) + 2 * Real.sqrt omega := by
            exact add_le_add hfourth_first' hfirst
      _ = 2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by ring
  have hthird : |thirdTerm - centerGM| ≤
      2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by
    rw [hthird_eq]
    exact hfourth
  constructor
  unfold sddErrorOp
  rw [hexpand]
  have hdecomp :
      firstTerm + secondTerm - thirdTerm - fourthTerm ≤
        |firstTerm - centerGM| + |secondTerm - centerGM| +
          |thirdTerm - centerGM| + |fourthTerm - centerGM| := by
    have hfirst_le : firstTerm - centerGM ≤ |firstTerm - centerGM| := by
      exact le_abs_self _
    have hsecond_le : secondTerm - centerGM ≤ |secondTerm - centerGM| := by
      exact le_abs_self _
    have hthird_le : -(thirdTerm - centerGM) ≤ |thirdTerm - centerGM| := by
      exact neg_le_abs _
    have hfourth_le : -(fourthTerm - centerGM) ≤ |fourthTerm - centerGM| := by
      exact neg_le_abs _
    have hrewrite :
        firstTerm + secondTerm - thirdTerm - fourthTerm =
          (firstTerm - centerGM) + (secondTerm - centerGM) -
            (thirdTerm - centerGM) - (fourthTerm - centerGM) := by
      ring
    rw [hrewrite]
    nlinarith
  have hmain_eq :
      switcherooAggregateFirstTerm params ψbi family M + secondTerm - thirdTerm - fourthTerm =
        firstTerm + secondTerm - thirdTerm - fourthTerm := by
    exact congrArg (fun t => t + secondTerm - thirdTerm - fourthTerm) hfirst_eq
  calc
    switcherooAggregateFirstTerm params ψbi family M +
        switcherooAggregateSecondTerm params ψbi family M -
        switcherooAggregateThirdTerm params ψbi family M -
        switcherooAggregateFourthTerm params ψbi family M
      = firstTerm + secondTerm - thirdTerm - fourthTerm := by
          simpa [secondTerm, thirdTerm, fourthTerm] using hmain_eq
    _
      ≤ |firstTerm - centerGM| + |secondTerm - centerGM| +
          |thirdTerm - centerGM| + |fourthTerm - centerGM| := hdecomp
    _ ≤ 2 * Real.sqrt omega + 2 * Real.sqrt zeta +
          (2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega) +
          (2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega) := by
            nlinarith [hfirst, hsecond', hthird, hfourth]
    _ = commutativitySwitcherooError zeta omega chi := by
          simp [commutativitySwitcherooError, Real.sqrt_eq_rpow]
          ring

end MIPStarRE.LDT.Pasting
