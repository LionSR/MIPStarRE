import MIPStarRE.LDT.Pasting.SwitcherooCompletion.SecondTerm

/-!
# Section 12 pasting: switcheroo theorem

The aggregate switcheroo theorem and its input conversions.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 200000 in
-- The four-term expansion + triangle chain still expands several explicit scalar
-- centers, but the tensor-order rewrites now come from reusable helper lemmas.
/-- `lem:commutativity-switcheroo`. -/
lemma commutativitySwitcheroo {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hperm : PermInvState ψbi)
    (hnorm : ψbi.IsNormalized)
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
  scalar center. We keep the two natural centers separate in the intermediate
  estimates:

  * `G ⊗ M` for the first term and the negative-term contraction chain
  * `M ⊗ G` for the second term

  The permutation-invariance hypothesis `hperm` then identifies these two
  centers at the end via `ev (A ⊗ B) = ev (B ⊗ A)`.
  -/
  refine ⟨?_⟩
  let 𝒟x : Distribution (SliceQuestion params) :=
    uniformDistribution (SliceQuestion params)
  let firstTerm := switcherooAggregateFirstTerm params ψbi family M
  let secondTerm := switcherooAggregateSecondTerm params ψbi family M
  let thirdTerm := switcherooAggregateThirdTerm params ψbi family M
  let fourthTerm := switcherooAggregateFourthTerm params ψbi family M
  let centerGM := switcherooAggregateTarget params ψbi family M
  let centerMGComplete : Error :=
    avgOver 𝒟x (fun y =>
      Preliminaries.middleSandwichExpectation ψbi 𝒟x
        (completePartProjFamily params family) (((M y).toSubMeas).total))
  have hfirst : |firstTerm - centerGM| ≤ 2 * Real.sqrt omega := by
    simpa [firstTerm, centerGM, switcherooAggregateFirstTerm_eq_leftSandwich,
      switcherooAggregateTarget_eq_middleSandwich] using
      switcheroo_first_term_close params ψbi hnorm family M omega hselfM
  have hsecond : |secondTerm - centerMGComplete| ≤ 2 * Real.sqrt zeta := by
    simpa [secondTerm, centerMGComplete, 𝒟x] using
      switcheroo_second_aggregate_term_close params ψbi hnorm family M zeta hselfG
  have hexpand :
      avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q => qSDDOp ψbi
            (switcherooAggregateLeft params family M q)
            (switcherooAggregateRight params family M q)) =
        firstTerm + secondTerm - thirdTerm - fourthTerm := by
    simpa [firstTerm, secondTerm, thirdTerm, fourthTerm] using
      switcherooAggregate_qSDDOp_expand_avg params ψbi family M
  have hthird_eq : thirdTerm = fourthTerm := by
    simpa [thirdTerm, fourthTerm] using
      switcherooAggregateThirdTerm_eq_fourthTerm params ψbi family M
  let onceCommuted : Error :=
    avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
      ∑ g : Polynomial params, ∑ o : Outcome,
        ev ψbi
          (leftTensor (ι₂ := ι)
            ((completePartSubMeas params family q.1).total *
              (M q.2).outcome o *
              (family.meas q.1).outcome g *
              (M q.2).outcome o *
              (family.meas q.1).outcome g)))
  let mixed : Error :=
    avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
      ∑ g : Polynomial params, ∑ o : Outcome,
        ev ψbi
          ((leftTensor (ι₂ := ι)
            ((completePartSubMeas params family q.1).total *
              (M q.2).outcome o *
              (family.meas q.1).outcome g *
              (M q.2).outcome o)) *
            rightTensor (ι₁ := ι) ((family.meas q.1).outcome g)))
  let leftFront : Error :=
    MIPStarRE.LDT.Pasting.switcherooLeftFrontCoreScalar params ψbi family M
  let firstSplit : Error :=
    MIPStarRE.LDT.Pasting.switcherooFirstSplitCoreScalar params ψbi family M
  let Gtotal : Fq params → MIPStarRE.Quantum.Op ι := fun x =>
    (completePartSubMeas params family x).total
  let Mtotal : Fq params → MIPStarRE.Quantum.Op ι := fun y =>
    ((M y).toSubMeas).total
  have hcenterMG_pair :
      centerMGComplete =
        avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ev ψbi (opTensor (Mtotal q.2) (Gtotal q.1))) := by
    simpa [centerMGComplete, Mtotal, Gtotal, 𝒟x] using
      switcherooAggregateMGCenterComplete_eq_opTensor_avg params ψbi family M
  have hcenterGM_pair :
      centerGM =
        avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ev ψbi (opTensor (Gtotal q.1) (Mtotal q.2))) := by
    simpa [centerGM, Gtotal, Mtotal] using
      switcherooAggregateTarget_eq_opTensor_avg params ψbi family M
  have hcenter_eq : centerMGComplete = centerGM := by
    rw [hcenterMG_pair, hcenterGM_pair]
    apply avgOver_congr
    intro q
    simpa [Gtotal, Mtotal] using hperm.ev_opTensor_swap (Mtotal q.2) (Gtotal q.1)
  have honce_prod_eq :
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ go : Polynomial params × Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1))) = onceCommuted := by
    unfold onceCommuted
    apply avgOver_congr
    intro q
    simpa using
      (Fintype.sum_prod_type' (f := fun g o =>
        ev ψbi
          (leftTensor (ι₂ := ι)
            ((completePartSubMeas params family q.1).total *
              (M q.2).outcome o *
              (family.meas q.1).outcome g *
              (M q.2).outcome o *
              (family.meas q.1).outcome g))))
  have hfourth_once_raw :
      |fourthTerm -
          avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
            ∑ go : Polynomial params × Outcome,
              ev ψbi
                (leftTensor (ι₂ := ι)
                  ((completePartSubMeas params family q.1).total *
                    (M q.2).outcome go.2 *
                    (family.meas q.1).outcome go.1 *
                    (M q.2).outcome go.2 *
                    (family.meas q.1).outcome go.1)))| ≤ Real.sqrt chi := by
    simpa [fourthTerm] using
      switcherooAggregateFourthTerm_split_close_once_commuted params ψbi hnorm family M chi hcomm
  have hfourth_once : |fourthTerm - onceCommuted| ≤ Real.sqrt chi := by
    rwa [honce_prod_eq] at hfourth_once_raw
  have honce_mixed : |onceCommuted - mixed| ≤ Real.sqrt zeta := by
    simpa [onceCommuted, mixed] using
      (switcherooAggregateFourthTerm_once_commuted_close_mixed
        params ψbi hnorm family M zeta hselfG)
  have hmixed_eq :
      mixed =
        avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ g : Polynomial params, ∑ o : Outcome,
            ev ψbi
              (rightTensor (ι₁ := ι) ((family.meas q.1).outcome g) *
                leftTensor (ι₂ := ι)
                  ((completePartSubMeas params family q.1).total *
                    (M q.2).outcome o *
                    (family.meas q.1).outcome g *
                    (M q.2).outcome o))) := by
    simpa [mixed] using
      switcherooMixed_eq_rightTensor_leftTensor
        (params := params) (ψbi := ψbi) (family := family) (M := M)
  have hleftFront_eq :
      leftFront =
        avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ g : Polynomial params, ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι) ((family.meas q.1).outcome g) *
                leftTensor (ι₂ := ι)
                  ((completePartSubMeas params family q.1).total *
                    (M q.2).outcome o *
                    (family.meas q.1).outcome g *
                    (M q.2).outcome o))) := by
    simpa [leftFront] using
      switcherooLeftFrontCoreScalar_eq_leftTensor_mul_leftTensor
        (params := params) (ψbi := ψbi) (family := family) (M := M)
  have hmixed_leftFront : |mixed - leftFront| ≤ Real.sqrt zeta := by
    rw [hmixed_eq, hleftFront_eq, abs_sub_comm]
    exact switcherooAggregateFourthTerm_mixed_close_left_front_raw
      params ψbi hnorm family M zeta hselfG
  have hleftFront_firstSplit :
      |leftFront - firstSplit| ≤ Real.sqrt chi := by
    change |switcherooLeftFrontCoreScalar params ψbi family M -
            switcherooFirstSplitCoreScalar params ψbi family M| ≤ Real.sqrt chi
    exact switcherooLeftFront_close_firstSplitCore
      params ψbi hnorm family M chi hcomm
  have hfirstSplit_eq : firstSplit = firstTerm := by
    change switcherooFirstSplitCoreScalar params ψbi family M =
        switcherooAggregateFirstTerm params ψbi family M
    exact switcherooAggregateFirstTerm_eq_split_by_g params ψbi family M
  -- Triangle-inequality chain: |fourthTerm - firstTerm| ≤ 2·√ζ + 2·√χ.
  have hfourth_firstTerm :
      |fourthTerm - firstTerm| ≤ 2 * Real.sqrt zeta + 2 * Real.sqrt chi := by
    rw [← hfirstSplit_eq]
    have hchain :
        |fourthTerm - firstSplit| ≤
          Real.sqrt chi + Real.sqrt zeta +
            (Real.sqrt zeta + Real.sqrt chi) := by
      calc
        |fourthTerm - firstSplit|
            ≤ |fourthTerm - onceCommuted| + |onceCommuted - firstSplit| :=
              abs_sub_le _ _ _
        _ ≤ |fourthTerm - onceCommuted| +
              (|onceCommuted - mixed| + |mixed - firstSplit|) := by
              gcongr
              exact abs_sub_le _ _ _
        _ ≤ |fourthTerm - onceCommuted| +
              (|onceCommuted - mixed| +
                (|mixed - leftFront| + |leftFront - firstSplit|)) := by
              gcongr
              exact abs_sub_le _ _ _
        _ ≤ Real.sqrt chi +
              (Real.sqrt zeta + (Real.sqrt zeta + Real.sqrt chi)) := by
              gcongr
        _ = Real.sqrt chi + Real.sqrt zeta +
              (Real.sqrt zeta + Real.sqrt chi) := by ring
    linarith [hchain]
  have hsecond_centerGM : |secondTerm - centerGM| ≤ 2 * Real.sqrt zeta := by
    rw [← hcenter_eq]; exact hsecond
  have hfourth_centerGM :
      |fourthTerm - centerGM| ≤
        2 * Real.sqrt omega + 2 * Real.sqrt zeta + 2 * Real.sqrt chi := by
    calc
      |fourthTerm - centerGM|
          ≤ |fourthTerm - firstTerm| + |firstTerm - centerGM| :=
            abs_sub_le _ _ _
      _ ≤ (2 * Real.sqrt zeta + 2 * Real.sqrt chi) + 2 * Real.sqrt omega := by
            gcongr
      _ = 2 * Real.sqrt omega + 2 * Real.sqrt zeta + 2 * Real.sqrt chi := by
            ring
  -- Discharge the SDDOpRel goal: show the averaged squared-distance defect is
  -- below the displayed error.
  refine ⟨?_⟩
  have hreduce :
      sddErrorOp ψbi (uniformDistribution (SlicePairQuestion params))
          (switcherooAggregateLeft params family M)
          (switcherooAggregateRight params family M) =
        firstTerm + secondTerm - 2 * fourthTerm := by
    unfold sddErrorOp
    rw [hexpand, hthird_eq]; ring
  rw [hreduce]
  have habs :
      |firstTerm + secondTerm - 2 * fourthTerm| ≤
        6 * Real.sqrt zeta + 6 * Real.sqrt omega + 4 * Real.sqrt chi := by
    have hsplit :
        firstTerm + secondTerm - 2 * fourthTerm =
          (firstTerm - centerGM) + (secondTerm - centerGM) -
            2 * (fourthTerm - centerGM) := by ring
    rw [hsplit]
    calc
      |((firstTerm - centerGM) + (secondTerm - centerGM)) -
            2 * (fourthTerm - centerGM)|
          ≤ |(firstTerm - centerGM) + (secondTerm - centerGM)| +
              |2 * (fourthTerm - centerGM)| := abs_sub _ _
      _ ≤ (|firstTerm - centerGM| + |secondTerm - centerGM|) +
              2 * |fourthTerm - centerGM| := by
            refine add_le_add (abs_add_le _ _) ?_
            rw [abs_mul]
            simp
      _ ≤ 2 * Real.sqrt omega + 2 * Real.sqrt zeta +
              2 * (2 * Real.sqrt omega + 2 * Real.sqrt zeta +
                2 * Real.sqrt chi) := by
            gcongr
      _ = 6 * Real.sqrt zeta + 6 * Real.sqrt omega + 4 * Real.sqrt chi := by
            ring
  calc
    firstTerm + secondTerm - 2 * fourthTerm
        ≤ |firstTerm + secondTerm - 2 * fourthTerm| := le_abs_self _
    _ ≤ 6 * Real.sqrt zeta + 6 * Real.sqrt omega + 4 * Real.sqrt chi := habs
    _ = commutativitySwitcherooError zeta omega chi := by
          simp [commutativitySwitcherooError, Real.sqrt_eq_rpow]

/-- Reindexing a uniform slice-pair average along `Prod.swap` preserves `SDDOpRel`. -/
lemma sddOpRel_swap_questions
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (A B : IdxOpFamily (SlicePairQuestion params) Outcome (ι × ι))
    (δ : Error) :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      A B δ →
      SDDOpRel ψbi
        (uniformDistribution (SlicePairQuestion params))
        (fun q => A (q.2, q.1))
        (fun q => B (q.2, q.1))
        δ := by
  intro ⟨hAB⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDOp ψbi (A (q.2, q.1)) (B (q.2, q.1)))
      =
        avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q => qSDDOp ψbi (A q) (B q)) := by
            symm
            simpa [SlicePairQuestion] using
              (avgOver_uniform_equiv
                (α := SlicePairQuestion params)
                (β := SlicePairQuestion params)
                (Equiv.prodComm (Fq params) (Fq params))
                (fun q => qSDDOp ψbi (A q) (B q)))
    _ ≤ δ := hAB

/-- Reinterpret the point-with-complete-part commutation bound as a relation on the
`Polynomial × Unit` outcome type expected by `commutativitySwitcheroo`. -/
lemma pointWithCompletePart_as_switcheroo_input
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma : Error)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (completePartPointProductLeft params family)
      (completePartPointProductRight params family)
      gamma) :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family (completePartProjFamily params family))
      (switcherooPointProductRight params family (completePartProjFamily params family))
      gamma := by
  rcases hcomm with ⟨hcomm⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDOp ψbi
          (switcherooPointProductLeft params family (completePartProjFamily params family) q)
          (switcherooPointProductRight params family (completePartProjFamily params family) q))
      = avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q => qSDDOp ψbi
            (completePartPointProductLeft params family q)
            (completePartPointProductRight params family q)) := by
              apply avgOver_congr
              intro q
              unfold qSDDOp qSDDCore
              let F : Polynomial params × Unit → Error := fun ab =>
                ev ψbi
                  ((((switcherooPointProductLeft params family
                            (completePartProjFamily params family) q).outcome ab -
                          (switcherooPointProductRight params family
                            (completePartProjFamily params family) q).outcome ab)ᴴ) *
                      ((switcherooPointProductLeft params family
                            (completePartProjFamily params family) q).outcome ab -
                        (switcherooPointProductRight params family
                          (completePartProjFamily params family) q).outcome ab))
              change (∑ ab : Polynomial params × Unit, F ab) = _
              have hsplit :
                  (∑ ab : Polynomial params × Unit, F ab) =
                    ∑ g : Polynomial params, ∑ u : Unit, F (g, u) := by
                simpa [F] using
                  (Fintype.sum_prod_type' (f := fun g u => F (g, u)))
              have hsingle :
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
                    (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total :=
                postprocess_unit_outcome_eq_total ((family.meas q.2).toSubMeas)
              rw [hsplit]
              simp [F, switcherooPointProductLeft, switcherooPointProductRight,
                completePartProjFamily, completePartPointProductLeft,
                completePartPointProductRight, completePartSubMeas,
                multiplyByTotalOnRight, multiplyByTotalOnLeft,
                orderedProductOpFamily, reversedProductOpFamily,
                OpFamily.leftPlacedOpFamily, postprocess_total, hsingle]
    _ ≤ gamma := hcomm

/-- The complete-part family inherits self-consistency from the slice family by
pointwise comparison of the `qSDD` defect. -/
lemma completePartProjFamily_selfConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : GCompleteSelfConsistencyStatement params strategy.state family zeta) :
    SDDRel strategy.state
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params (completePartProjFamily params family))
      (switcherooSelfConsistencyRight params (completePartProjFamily params family))
      zeta := by
  simpa using
    completePartProjFamily_selfConsistency_generic params strategy.state family zeta hself

end MIPStarRE.LDT.Pasting
