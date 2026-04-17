import MIPStarRE.LDT.Pasting.SwitcherooContraction

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

/-- Contraction witness for the final `sqrt chi` left-front overlap step. -/
private lemma switcherooAggregateLeftFront_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    (∑ go : Polynomial params × Outcome,
        (∑ u : Unit,
            leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ *
          (∑ u : Unit,
            leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))) ≤ 1 := by
  calc
    (∑ go : Polynomial params × Outcome,
        (∑ u : Unit,
            leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ *
          (∑ u : Unit,
            leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)))
      = ∑ go : Polynomial params × Outcome,
          leftTensor (ι₂ := ι)
            ((M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2) := by
            refine Finset.sum_congr rfl ?_
            intro go _
            calc
              (∑ u : Unit,
                  leftTensor (ι₂ := ι)
                    (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ *
                (∑ u : Unit,
                  leftTensor (ι₂ := ι)
                    (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))
                = (leftTensor (ι₂ := ι)
                    (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ *
                    leftTensor (ι₂ := ι)
                      (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2) := by
                        simp
              _ = leftTensor (ι₂ := ι)
                    ((((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)ᴴ *
                      (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)) := by
                        rw [show
                          (leftTensor (ι₂ := ι)
                              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ =
                            leftTensor (ι₂ := ι)
                              ((((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)ᴴ) by
                              simpa [leftTensor, opTensor] using
                                (conjTranspose_opTensor
                                  (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)
                                  (1 : MIPStarRE.Quantum.Op ι))]
                        rw [leftTensor_mul_leftTensor]
              _ = leftTensor (ι₂ := ι)
                    ((M q.2).outcome go.2 *
                      (family.meas q.1).outcome go.1 *
                      (M q.2).outcome go.2) := by
                        congr 1
                        have hGherm : ((family.meas q.1).outcome go.1)ᴴ =
                            (family.meas q.1).outcome go.1 :=
                          (family.meas q.1).outcome_hermitian go.1
                        have hMoherm : ((M q.2).outcome go.2)ᴴ =
                            (M q.2).outcome go.2 :=
                          (M q.2).outcome_hermitian go.2
                        calc
                          ((((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)ᴴ) *
                              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)
                            = (((M q.2).outcome go.2) * (family.meas q.1).outcome go.1) *
                                (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2) := by
                                    simp [Matrix.conjTranspose_mul, hGherm, hMoherm]
                          _ = (M q.2).outcome go.2 *
                                ((family.meas q.1).outcome go.1 * (family.meas q.1).outcome go.1) *
                                (M q.2).outcome go.2 := by
                                    simp [mul_assoc]
                          _ = (M q.2).outcome go.2 *
                                (family.meas q.1).outcome go.1 *
                                (M q.2).outcome go.2 := by
                                    rw [(family.meas q.1).proj go.1]
    _ = ∑ o : Outcome,
          leftTensor (ι₂ := ι)
            ((M q.2).outcome o * (completePartSubMeas params family q.1).total *
              (M q.2).outcome o) := by
            calc
              ∑ go : Polynomial params × Outcome,
                  leftTensor (ι₂ := ι)
                    ((M q.2).outcome go.2 *
                      (family.meas q.1).outcome go.1 *
                      (M q.2).outcome go.2)
                = ∑ g : Polynomial params,
                    ∑ o : Outcome,
                      leftTensor (ι₂ := ι)
                        ((M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o) := by
                          simpa using
                            (Fintype.sum_prod_type' (f := fun g o =>
                              leftTensor (ι₂ := ι)
                                ((M q.2).outcome o *
                                  (family.meas q.1).outcome g *
                                  (M q.2).outcome o)))
              _ = ∑ o : Outcome,
                    ∑ g : Polynomial params,
                      leftTensor (ι₂ := ι)
                        ((M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o) := by
                          rw [Finset.sum_comm]
              _ = ∑ o : Outcome,
                    leftTensor (ι₂ := ι)
                      ((M q.2).outcome o * (completePartSubMeas params family q.1).total *
                        (M q.2).outcome o) := by
                          refine Finset.sum_congr rfl ?_
                          intro o _
                          rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ]
                          congr 1
                          calc
                            ∑ g : Polynomial params,
                                (M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o
                              = (M q.2).outcome o *
                                  (∑ g : Polynomial params, (family.meas q.1).outcome g) *
                                  (M q.2).outcome o := by
                                    simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
                            _ = (M q.2).outcome o * (completePartSubMeas params family q.1).total *
                                  (M q.2).outcome o := by
                                    rw [(family.meas q.1).sum_eq_total]
                                    simp [completePartSubMeas, postprocess_total]
    _ ≤ 1 := by
          rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ]
          have hGle : (completePartSubMeas params family q.1).total ≤ 1 :=
            (completePartSubMeas params family q.1).total_le_one
          have hmid_le :
              ∑ o : Outcome,
                  (M q.2).outcome o * (completePartSubMeas params family q.1).total *
                    (M q.2).outcome o ≤ 1 := by
            exact projSubMeas_sandwich_sum_le_one (M q.2)
              ((completePartSubMeas params family q.1).total) hGle
          calc
            leftTensor (ι₂ := ι)
                (∑ o : Outcome,
                  (M q.2).outcome o * (completePartSubMeas params family q.1).total *
                    (M q.2).outcome o)
              ≤ leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) := by
                  simpa [leftTensor, opTensor] using
                    (opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
                      hmid_le (show (0 : MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one))
            _ = 1 := by simp [leftTensor]

set_option maxHeartbeats 3000000 in
/-- Average the single-question four-term `qSDDOp` expansion over the
slice-pair distribution. -/
private lemma switcherooAggregate_qSDDOp_expand_avg
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDOp ψbi
          (switcherooAggregateLeft params family M q)
          (switcherooAggregateRight params family M q)) =
      switcherooAggregateFirstTerm params ψbi family M +
        switcherooAggregateSecondTerm params ψbi family M -
        switcherooAggregateThirdTerm params ψbi family M -
        switcherooAggregateFourthTerm params ψbi family M := by
  let A : SlicePairQuestion params → Error := fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o))
  let B : SlicePairQuestion params → Error := fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))
  let C : SlicePairQuestion params → Error := fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))
  let D : SlicePairQuestion params → Error := fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o))
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q => qSDDOp ψbi
          (switcherooAggregateLeft params family M q)
          (switcherooAggregateRight params family M q))
      = avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q => A q + B q - C q - D q) := by
              apply avgOver_congr
              intro q
              rw [switcherooAggregate_qSDDOp_expand]
              simp [A, B, C, D, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = avgOver (uniformDistribution (SlicePairQuestion params)) A +
          avgOver (uniformDistribution (SlicePairQuestion params)) B -
          avgOver (uniformDistribution (SlicePairQuestion params)) C -
          avgOver (uniformDistribution (SlicePairQuestion params)) D := by
            rw [show (fun q => A q + B q - C q - D q) =
                fun q => (A q + B q) + ((-1 : Error) * C q + (-1 : Error) * D q) by
                  funext q
                  ring]
            rw [avgOver_add, avgOver_add, avgOver_add, avgOver_const_mul, avgOver_const_mul]
            simp [sub_eq_add_neg]
            ring
    _ = switcherooAggregateFirstTerm params ψbi family M +
          switcherooAggregateSecondTerm params ψbi family M -
          switcherooAggregateThirdTerm params ψbi family M -
          switcherooAggregateFourthTerm params ψbi family M := by
            simp [switcherooAggregateFirstTerm, switcherooAggregateSecondTerm,
              switcherooAggregateThirdTerm, switcherooAggregateFourthTerm, A, B, C, D]

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
private lemma switcheroo_second_aggregate_term_close
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

-- The four-term expansion + triangle chain involves many `simpa`/`calc` steps.
set_option maxHeartbeats 400000 in
/-- `lem:commutativity-switcheroo`. -/
lemma commutativitySwitcheroo {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (_hperm : PermInvState ψbi)
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

/-- Expand the left aggregate family after replacing the slice family by its
completed one-outcome form. -/
private lemma switcherooAggregateLeft_completePart_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (switcherooAggregateLeft params family (completePartProjFamily params family) q).outcome () =
      (completePartTotalProductLeft params family q).outcome () := by
  have hsingle1 :
      (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).outcome () =
        (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).total :=
    postprocess_unit_outcome_eq_total ((family.meas q.1).toSubMeas)
  have hsingle2 :
      (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
        (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total :=
    postprocess_unit_outcome_eq_total ((family.meas q.2).toSubMeas)
  simp [switcherooAggregateLeft, completePartProjFamily,
    completePartTotalProductLeft, multiplyByTotalOnRight,
    multiplyByTotalOnLeft, OpFamily.leftPlacedOpFamily]

/-- Expand the right aggregate family after replacing the slice family by its
completed one-outcome form. -/
private lemma switcherooAggregateRight_completePart_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (switcherooAggregateRight params family (completePartProjFamily params family) q).outcome () =
      (completePartTotalProductRight params family q).outcome () := by
  have hsingle1 :
      (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).outcome () =
        (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).total :=
    postprocess_unit_outcome_eq_total ((family.meas q.1).toSubMeas)
  have hsingle2 :
      (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
        (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total :=
    postprocess_unit_outcome_eq_total ((family.meas q.2).toSubMeas)
  simp [switcherooAggregateRight, completePartProjFamily,
    completePartTotalProductRight, multiplyByTotalOnRight,
    multiplyByTotalOnLeft, OpFamily.leftPlacedOpFamily]

private lemma qSDDOp_congr_unit_outcome
    (ψbi : QuantumState (ι × ι))
    (A B A' B' : OpFamily Unit (ι × ι))
    (hA : A.outcome () = A'.outcome ())
    (hB : B.outcome () = B'.outcome ()) :
    qSDDOp ψbi A B = qSDDOp ψbi A' B' := by
  unfold qSDDOp qSDDCore
  simp [hA, hB]

lemma completePartAggregateCommutation_as_total
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma : Error)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooAggregateLeft params family (completePartProjFamily params family))
      (switcherooAggregateRight params family (completePartProjFamily params family))
      gamma) :
    SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (completePartTotalProductLeft params family)
      (completePartTotalProductRight params family)
      gamma := by
  rcases hcomm with ⟨hcomm⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q =>
          qSDDOp ψbi
            (completePartTotalProductLeft params family q)
            (completePartTotalProductRight params family q))
      = avgOver (uniformDistribution (SlicePairQuestion params))
          (fun q =>
            qSDDOp ψbi
              (switcherooAggregateLeft params family (completePartProjFamily params family) q)
              (switcherooAggregateRight params family
                (completePartProjFamily params family) q)) := by
                apply avgOver_congr
                intro q
                symm
                exact qSDDOp_congr_unit_outcome ψbi
                  _ _ _ _
                  (switcherooAggregateLeft_completePart_outcome params family q)
                  (switcherooAggregateRight_completePart_outcome params family q)
    _ ≤ gamma := hcomm

set_option maxHeartbeats 1000000 in
-- Many sqrt/rpow manipulations for `12 * sqrt zeta + 4 * sqrt (ν_com) ≤ ν₂`.
lemma firstSwitcherooError_le_commutingWithGCompleteError
    (params : Parameters) [FieldModel params.q]
    (gamma zeta : Error)
    (hgamma_nonneg : 0 ≤ gamma) (hgamma : gamma ≤ 1)
    (hzeta_nonneg : 0 ≤ zeta) (hzeta : zeta ≤ 1)
    (hd_le_q : params.d ≤ params.q) :
    commutativitySwitcherooError zeta zeta
      (Commutativity.comMainError params gamma zeta)
      ≤ commutingWithGCompleteError params gamma zeta := by
  have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hq_pos : (0 : Error) < params.q := by
    exact_mod_cast params.hq
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  have hratio_le_one : ((params.d : Error) / (params.q : Error)) ≤ 1 := by
    exact (div_le_one hq_pos).2 (by simpa using hd_le_q)
  let quarterSum : Error :=
    Real.rpow gamma (1 / (4 : Error)) +
      Real.rpow zeta (1 / (4 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error))
  let eighthSum : Error :=
    Real.rpow gamma (1 / (8 : Error)) +
      Real.rpow zeta (1 / (8 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))
  let sixteenthSum : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
  have hhalf_zeta :
      Real.rpow zeta (1 / (2 : Error)) ≤ Real.rpow zeta (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 / (2 : Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
  have heighth_gamma :
      Real.rpow gamma (1 / (8 : Error)) ≤ Real.rpow gamma (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 / (8 : Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hgamma_nonneg hgamma (by norm_num) hpow
  have heighth_zeta :
      Real.rpow zeta (1 / (8 : Error)) ≤ Real.rpow zeta (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 / (8 : Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta (by norm_num) hpow
  have heighth_ratio :
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error)) ≤
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    have hpow : (1 / (16 : Error)) ≤ (1 / (8 : Error)) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_ge' hratio_nonneg hratio_le_one (by norm_num) hpow
  have hsixteenth_nonneg : 0 ≤ sixteenthSum := by
    dsimp [sixteenthSum]
    positivity
  have hsqrt_m_le : Real.sqrt (params.m : Error) ≤ (params.m : Error) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hm_nonneg
    · nlinarith
  have heighth_le_sixteenth : eighthSum ≤ sixteenthSum := by
    dsimp [eighthSum, sixteenthSum]
    exact add_le_add (add_le_add heighth_gamma heighth_zeta) heighth_ratio
  have hgamma_eight_sq :
      (Real.rpow gamma (1 / (8 : Error))) ^ (2 : ℕ) =
        Real.rpow gamma (1 / (4 : Error)) := by
    calc
      (Real.rpow gamma (1 / (8 : Error))) ^ (2 : ℕ)
          = (Real.rpow gamma (1 / (8 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow gamma ((1 / (8 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hgamma_nonneg _ _
      _ = Real.rpow gamma (1 / (4 : Error)) := by norm_num
  have hzeta_eight_sq :
      (Real.rpow zeta (1 / (8 : Error))) ^ (2 : ℕ) =
        Real.rpow zeta (1 / (4 : Error)) := by
    calc
      (Real.rpow zeta (1 / (8 : Error))) ^ (2 : ℕ)
          = (Real.rpow zeta (1 / (8 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow zeta ((1 / (8 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hzeta_nonneg _ _
      _ = Real.rpow zeta (1 / (4 : Error)) := by norm_num
  have hratio_eight_sq :
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))) ^ (2 : ℕ) =
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) := by
    calc
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))) ^ (2 : ℕ)
          =
            (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))) ^
              (2 : Error) := by norm_num
      _ =
          Real.rpow (((params.d : Error) / (params.q : Error)))
            ((1 / (8 : Error)) * (2 : Error)) := by
              symm
              exact Real.rpow_mul hratio_nonneg _ _
      _ = Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (4 : Error)) := by
            norm_num
  have hquarter_le_eighth_sq : quarterSum ≤ eighthSum ^ (2 : ℕ) := by
    let a : Error := Real.rpow gamma (1 / (8 : Error))
    let b : Error := Real.rpow zeta (1 / (8 : Error))
    let c : Error := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (8 : Error))
    have ha_nonneg : 0 ≤ a := by
      dsimp [a]
      positivity
    have hb_nonneg : 0 ≤ b := by
      dsimp [b]
      positivity
    have hc_nonneg : 0 ≤ c := by
      dsimp [c]
      positivity
    have hsq : a ^ (2 : ℕ) + b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ (a + b + c) ^ (2 : ℕ) := by
      nlinarith [ha_nonneg, hb_nonneg, hc_nonneg]
    rw [hgamma_eight_sq, hzeta_eight_sq, hratio_eight_sq] at hsq
    simpa [a, b, c, quarterSum, eighthSum] using hsq
  have hsqrt_quarter : Real.sqrt quarterSum ≤ eighthSum := by
    have heighth_nonneg : 0 ≤ eighthSum := by
      dsimp [eighthSum]
      positivity
    exact (Real.sqrt_le_iff).2 ⟨heighth_nonneg, by simpa using hquarter_le_eighth_sq⟩
  have hsqrt30_le_six : Real.sqrt (30 : Error) ≤ 6 := by
    have hsq : (Real.sqrt (30 : Error)) ^ (2 : ℕ) ≤ (6 : Error) ^ (2 : ℕ) := by norm_num
    nlinarith [Real.sq_sqrt (show 0 ≤ (30 : Error) by positivity), hsq]
  have hsqrt_m_le : Real.sqrt (params.m : Error) ≤ (params.m : Error) := by
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hm_nonneg
    · nlinarith
  have hsqrt_com :
      Real.sqrt (Commutativity.comMainError params gamma zeta) ≤
        6 * (params.m : Error) * sixteenthSum := by
    have hquarter_nonneg : 0 ≤ quarterSum := by
      dsimp [quarterSum]
      positivity
    have hsplit_m_quarter :
        Real.sqrt ((params.m : Error) * quarterSum) =
          Real.sqrt (params.m : Error) * Real.sqrt quarterSum := by
      rw [Real.sqrt_mul hm_nonneg]
    calc
      Real.sqrt (Commutativity.comMainError params gamma zeta)
          = Real.sqrt (30 : Error) *
              Real.sqrt ((params.m : Error) * quarterSum) := by
              simp [Commutativity.comMainError, quarterSum]
              ring
      _ = Real.sqrt (30 : Error) * (Real.sqrt (params.m : Error) * Real.sqrt quarterSum) := by
            rw [hsplit_m_quarter]
      _ = Real.sqrt (30 : Error) * Real.sqrt (params.m : Error) * Real.sqrt quarterSum := by
            ring
      _ ≤ 6 * (params.m : Error) * eighthSum := by
            gcongr
      _ ≤ 6 * (params.m : Error) * sixteenthSum := by
            gcongr
  have hzeta_term :
      12 * Real.rpow zeta (1 / (2 : Error)) ≤ 12 * (params.m : Error) * sixteenthSum := by
    have hterm : Real.rpow zeta (1 / (2 : Error)) ≤ sixteenthSum := by
      have hgamma16_nonneg : 0 ≤ Real.rpow gamma (1 / (16 : Error)) := by
        exact Real.rpow_nonneg hgamma_nonneg _
      have hratio16_nonneg :
          0 ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
        exact Real.rpow_nonneg hratio_nonneg _
      have hsum1 :
          Real.rpow zeta (1 / (16 : Error)) ≤
            Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) := by
        linarith
      have hsum2 :
          Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) ≤
            sixteenthSum := by
        have hsum2' :
            Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) ≤
              Real.rpow gamma (1 / (16 : Error)) + Real.rpow zeta (1 / (16 : Error)) +
                Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
          linarith
        simpa [sixteenthSum] using hsum2'
      exact le_trans hhalf_zeta (le_trans hsum1 hsum2)
    nlinarith [hm_ge_one, hterm]
  have hchi_term :
      4 * Real.rpow (Commutativity.comMainError params gamma zeta) (1 / (2 : Error)) ≤
        24 * (params.m : Error) * sixteenthSum := by
    have hsqrt_com' :
        Real.rpow (Commutativity.comMainError params gamma zeta) (1 / (2 : Error)) ≤
          6 * (params.m : Error) * sixteenthSum := by
      simpa [Real.sqrt_eq_rpow] using hsqrt_com
    nlinarith [hsqrt_com']
  calc
    commutativitySwitcherooError zeta zeta (Commutativity.comMainError params gamma zeta)
      = 12 * Real.rpow zeta (1 / (2 : Error)) +
          4 * Real.rpow (Commutativity.comMainError params gamma zeta) (1 / (2 : Error)) := by
            simp [commutativitySwitcherooError]
            ring
    _ ≤ 12 * (params.m : Error) * sixteenthSum +
          24 * (params.m : Error) * sixteenthSum := by
            nlinarith [hzeta_term, hchi_term]
    _ = commutingWithGCompleteError params gamma zeta := by
          simp [commutingWithGCompleteError, sixteenthSum]
          ring


end MIPStarRE.LDT.Pasting
