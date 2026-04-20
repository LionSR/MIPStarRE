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

-- The four-term expansion + triangle chain involves many `simpa`/`calc` steps.
set_option maxHeartbeats 400000 in
/-- `lem:commutativity-switcheroo`. -/
lemma commutativitySwitcheroo {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
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
  constructor
  unfold sddErrorOp
  rw [hexpand]
  /-
  Remaining blocker: the fourth-term chain is reduced to packaging the raw helper
  bounds into a final negative-term estimate and then transferring it to the third
  term via `hthird_eq`.
  -/
  sorry

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
