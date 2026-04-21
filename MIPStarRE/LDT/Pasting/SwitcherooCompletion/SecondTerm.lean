import MIPStarRE.LDT.Pasting.SwitcherooCompletion.Expansion

/-!
# Section 12 pasting: switcheroo second term

Complete-part self-consistency and the second switcheroo term.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The one-outcome complete-part family inherits self-consistency from the slice family. -/
lemma completePartProjFamily_selfConsistency_generic
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hself : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (switcherooSelfConsistencyLeft params (completePartProjFamily params family))
      (switcherooSelfConsistencyRight params (completePartProjFamily params family))
      zeta := by
  rcases hself.completePartSelfConsistency with ⟨hself_bound⟩
  constructor
  unfold sddError at *
  calc
    avgOver (uniformDistribution (SliceQuestion params))
        (fun x =>
          qSDD ψbi
            ((switcherooSelfConsistencyLeft params (completePartProjFamily params family)) x)
            ((switcherooSelfConsistencyRight params (completePartProjFamily params family)) x))
      ≤
        avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            qSDD ψbi
              ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas)) x)
              ((IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)) x)) := by
            apply avgOver_mono
            intro x
            simpa [switcherooSelfConsistencyLeft, switcherooSelfConsistencyRight,
              completePartProjFamily, IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
              qSDD_completePart_le_slice params ψbi family x
    _ ≤ zeta := hself_bound

/-- The second positive switcheroo term is close to the swapped center coming
from the complete-part family.

This aggregate form matches the four-term `qSDDOp` expansion: the projective
family in the sandwich is the one-outcome complete part `G^x`, not the original
slice-outcome family. -/
lemma switcheroo_second_aggregate_term_close
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    let secondTerm := switcherooAggregateSecondTerm params ψbi family M
    let commonTerm :=
      avgOver (uniformDistribution (SliceQuestion params))
        (fun y => Preliminaries.middleSandwichExpectation ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartProjFamily params family) (((M y).toSubMeas).total))
    |secondTerm - commonTerm| ≤ 2 * Real.sqrt zeta := by
  let 𝒟x : Distribution (SliceQuestion params) := uniformDistribution (SliceQuestion params)
  let Gcomplete : IdxProjSubMeas (SliceQuestion params) Unit ι :=
    completePartProjFamily params family
  let L : Fq params → Error := fun y =>
    Preliminaries.leftSandwichExpectation ψbi 𝒟x Gcomplete (((M y).toSubMeas).total)
  let C : Fq params → Error := fun y =>
    Preliminaries.middleSandwichExpectation ψbi 𝒟x Gcomplete (((M y).toSubMeas).total)
  change |switcherooAggregateSecondTerm params ψbi family M - avgOver 𝒟x C| ≤
    2 * Real.sqrt zeta
  have hselfG_complete :
      SDDRel ψbi 𝒟x
        (switcherooSelfConsistencyLeft params Gcomplete)
        (switcherooSelfConsistencyRight params Gcomplete)
        zeta := by
    simpa [𝒟x, Gcomplete] using
      completePartProjFamily_selfConsistency_generic params ψbi family zeta hselfG
  have hselfG_bip := switcherooSelfConsistency_bip params ψbi Gcomplete zeta hselfG_complete
  have hpoint : ∀ y, |L y - C y| ≤ 2 * Real.sqrt zeta := by
    intro y
    have hB : Preliminaries.OpBounded01 (((M y).toSubMeas).total) := by
      refine ⟨?_, ?_⟩
      · exact SubMeas.total_nonneg ((M y).toSubMeas)
      · exact sub_nonneg.mpr ((M y).toSubMeas).total_le_one
    simpa [L, C, 𝒟x, Gcomplete] using
      (Preliminaries.switchSandwich ψbi
        𝒟x
        hnorm
        (by simpa [𝒟x] using uniformDistribution_weight_sum_le_one (SliceQuestion params))
        Gcomplete
        (((M y).toSubMeas).total)
        hB
        zeta
        hselfG_bip).leftSandwichTransfer
  have hsecond_eq :
      switcherooAggregateSecondTerm params ψbi family M =
        avgOver 𝒟x L := by
    change
      avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q =>
            ∑ o : Outcome,
              ev ψbi
                (leftTensor
                  ((completePartSubMeas params family q.1).total * (M q.2).outcome o *
                    (completePartSubMeas params family q.1).total))) =
        avgOver 𝒟x L
    calc
      avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q =>
            ∑ o : Outcome,
              ev ψbi
                (leftTensor
                  ((completePartSubMeas params family q.1).total * (M q.2).outcome o *
                    (completePartSubMeas params family q.1).total)))
        = avgOver (uniformDistribution (SliceQuestion params))
            (fun y =>
              avgOver (uniformDistribution (SliceQuestion params))
                (fun x =>
                  ∑ o : Outcome,
                    ev ψbi
                      (leftTensor
                        ((completePartSubMeas params family x).total * (M y).outcome o *
                          (completePartSubMeas params family x).total)))) := by
              calc
                avgOver (uniformDistribution (SlicePairQuestion params))
                    (fun q =>
                      ∑ o : Outcome,
                        ev ψbi
                          (leftTensor
                            ((completePartSubMeas params family q.1).total *
                              (M q.2).outcome o *
                              (completePartSubMeas params family q.1).total))) =
                  avgOver (uniformDistribution (SlicePairQuestion params))
                    (fun q =>
                      ∑ o : Outcome,
                        ev ψbi
                          (leftTensor
                            ((completePartSubMeas params family q.2).total *
                              (M q.1).outcome o *
                              (completePartSubMeas params family q.2).total))) := by
                        simpa [SlicePairQuestion] using
                          (avgOver_uniform_equiv
                            (α := SlicePairQuestion params)
                            (β := SlicePairQuestion params)
                            (Equiv.prodComm (Fq params) (Fq params))
                            (fun q =>
                              ∑ o : Outcome,
                                ev ψbi
                                  (leftTensor
                                    ((completePartSubMeas params family q.1).total *
                                      (M q.2).outcome o *
                                      (completePartSubMeas params family q.1).total))))
                _ = avgOver (uniformDistribution (SliceQuestion params))
                      (fun y =>
                        avgOver (uniformDistribution (SliceQuestion params))
                          (fun x =>
                            ∑ o : Outcome,
                              ev ψbi
                                (leftTensor
                                  ((completePartSubMeas params family x).total *
                                    (M y).outcome o *
                                    (completePartSubMeas params family x).total)))) := by
                        simpa [SlicePairQuestion, SliceQuestion] using
                          (avgOver_uniform_prod
                            (α := SliceQuestion params)
                            (β := SliceQuestion params)
                            (f := fun y x =>
                              ∑ o : Outcome,
                                ev ψbi
                                  (leftTensor
                                    ((completePartSubMeas params family x).total *
                                      (M y).outcome o *
                                      (completePartSubMeas params family x).total))))
      _ = avgOver 𝒟x L := by
            apply avgOver_congr
            intro y
            unfold L Preliminaries.leftSandwichExpectation
            apply avgOver_congr
            intro x
            let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family x).total
            have hGout : (Gcomplete x).outcome () = G := by
              simpa [Gcomplete, completePartProjFamily, G, completePartSubMeas,
                postprocess] using (family.meas x).sum_eq_total
            calc
              ∑ o : Outcome,
                  ev ψbi (leftTensor (G * (M y).outcome o * G))
                = ev ψbi (leftTensor (G * ((M y).toSubMeas).total * G)) := by
                    rw [← ev_sum ψbi (fun o : Outcome =>
                      leftTensor (G * (M y).outcome o * G))]
                    rw [leftTensor_finset_sum]
                    congr 1
                    rw [← Finset.sum_mul, ← Finset.mul_sum, (M y).sum_eq_total]
              _ = ∑ _u : Unit,
                    ev ψbi
                      (leftTensor ((Gcomplete x).outcome ()) *
                        leftTensor (((M y).toSubMeas).total) *
                        leftTensor ((Gcomplete x).outcome ())) := by
                    simp [hGout, leftTensor_mul_leftTensor, mul_assoc]
  calc
    |switcherooAggregateSecondTerm params ψbi family M - avgOver 𝒟x C|
      = |avgOver 𝒟x L - avgOver 𝒟x C| := by rw [hsecond_eq]
    _ = |avgOver 𝒟x (fun y => L y - C y)| := by
          simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ ≤ avgOver 𝒟x (fun y => |L y - C y|) := by
          exact avgOver_abs_le_avgOver_abs _ _
    _ ≤ avgOver 𝒟x (fun _ => 2 * Real.sqrt zeta) := by
          exact avgOver_mono _ _ _ hpoint
    _ = 2 * Real.sqrt zeta := by
          simpa [𝒟x] using
            avgOver_uniform_const (α := SliceQuestion params) (2 * Real.sqrt zeta)

/-- The complete-part `M ⊗ G` switcheroo center, repackaged as a slice-pair
`opTensor` average over the `M`-totals and complete-part `G`-totals. -/
lemma switcherooAggregateMGCenterComplete_eq_opTensor_avg
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    avgOver (uniformDistribution (SliceQuestion params))
        (fun y =>
          Preliminaries.middleSandwichExpectation ψbi
            (uniformDistribution (SliceQuestion params))
            (completePartProjFamily params family) (((M y).toSubMeas).total)) =
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ev ψbi
          (opTensor
            (((M q.2).toSubMeas).total)
            ((completePartSubMeas params family q.1).total))) := by
  let 𝒟x : Distribution (SliceQuestion params) :=
    uniformDistribution (SliceQuestion params)
  let Mtotal : Fq params → MIPStarRE.Quantum.Op ι := fun y =>
    ((M y).toSubMeas).total
  let Gtotal : Fq params → MIPStarRE.Quantum.Op ι := fun x =>
    (completePartSubMeas params family x).total
  let F : Fq params → Fq params → Error := fun x y =>
    ∑ u : Unit,
      ev ψbi
        (leftTensor (ι₂ := ι) (Mtotal y) *
          rightTensor (ι₁ := ι) ((completePartProjFamily params family x).outcome u))
  calc
    avgOver 𝒟x (fun y =>
        Preliminaries.middleSandwichExpectation ψbi 𝒟x
          (completePartProjFamily params family) (((M y).toSubMeas).total))
      = avgOver 𝒟x (fun y => avgOver 𝒟x (fun x => F x y)) := by
        simp [F, 𝒟x, Preliminaries.middleSandwichExpectation, Mtotal]
    _ = avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q => F q.2 q.1) := by
        symm
        simpa [𝒟x, SlicePairQuestion, SliceQuestion] using
          (avgOver_uniform_prod
            (α := SliceQuestion params)
            (β := SliceQuestion params)
            (f := fun y x => F x y))
    _ = avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q => F q.1 q.2) := by
        symm
        simpa [SlicePairQuestion] using
          (avgOver_uniform_equiv
            (α := SlicePairQuestion params)
            (β := SlicePairQuestion params)
            (Equiv.prodComm (Fq params) (Fq params))
            (fun q => F q.1 q.2))
    _ = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ev ψbi
            (opTensor
              (((M q.2).toSubMeas).total)
              ((completePartSubMeas params family q.1).total))) := by
        apply avgOver_congr
        intro q
        rcases q with ⟨x, y⟩
        have hsingle :
            (completePartProjFamily params family x).outcome () = Gtotal x := by
          change (completePartSubMeas params family x).outcome () =
            (completePartSubMeas params family x).total
          simpa [completePartSubMeas] using
            postprocess_unit_outcome_eq_total ((family.meas x).toSubMeas)
        simp [F, Gtotal, Mtotal, hsingle, leftTensor_mul_rightTensor_eq_opTensor]

/-- The `G ⊗ M` switcheroo center, repackaged as a slice-pair `opTensor` average
over the complete-part `G`-totals and `M`-totals. -/
lemma switcherooAggregateTarget_eq_opTensor_avg
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooAggregateTarget params ψbi family M =
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ev ψbi
          (opTensor
            ((completePartSubMeas params family q.1).total)
            (((M q.2).toSubMeas).total))) := by
  let Mtotal : Fq params → MIPStarRE.Quantum.Op ι := fun y =>
    ((M y).toSubMeas).total
  let Gtotal : Fq params → MIPStarRE.Quantum.Op ι := fun x =>
    (completePartSubMeas params family x).total
  unfold switcherooAggregateTarget
  apply avgOver_congr
  intro q
  rcases q with ⟨x, y⟩
  calc
    ∑ o : Outcome,
        ev ψbi
          (leftTensor (ι₂ := ι) (Gtotal x) *
            rightTensor (ι₁ := ι) ((M y).outcome o))
      = ev ψbi
          (∑ o : Outcome,
            leftTensor (ι₂ := ι) (Gtotal x) *
              rightTensor (ι₁ := ι) ((M y).outcome o)) := by
          rw [← ev_sum ψbi (fun o : Outcome =>
            leftTensor (ι₂ := ι) (Gtotal x) *
              rightTensor (ι₁ := ι) ((M y).outcome o))]
    _ = ev ψbi
          (leftTensor (ι₂ := ι) (Gtotal x) *
            ∑ o : Outcome, rightTensor (ι₁ := ι) ((M y).outcome o)) := by
          congr 1
          exact (Finset.mul_sum
            (s := (Finset.univ : Finset Outcome))
            (f := fun o : Outcome => rightTensor (ι₁ := ι) ((M y).outcome o))
            (a := leftTensor (ι₂ := ι) (Gtotal x))).symm
    _ = ev ψbi
          (leftTensor (ι₂ := ι) (Gtotal x) *
            rightTensor (ι₁ := ι) (Mtotal y)) := by
          rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ
            (fun o : Outcome => (M y).outcome o)]
          rw [(M y).sum_eq_total]
    _ = ev ψbi (opTensor (Gtotal x) (Mtotal y)) := by
          simp [Gtotal, Mtotal, leftTensor_mul_rightTensor_eq_opTensor]

end MIPStarRE.LDT.Pasting
