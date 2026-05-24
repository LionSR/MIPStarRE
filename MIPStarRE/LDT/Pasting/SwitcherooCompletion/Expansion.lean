import MIPStarRE.LDT.Pasting.SwitcherooContraction.Raw

/-!
# Section 12 pasting: switcheroo expansion

Expansion identities and the left-front contraction bound.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Contraction witness for the final `sqrt chi` left-front overlap step. -/
lemma switcherooAggregateLeftFront_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    (∑ go : Polynomial params × Outcome,
        (∑ _u : Unit,
            leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ *
          (∑ _u : Unit,
            leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))) ≤ 1 := by
  calc
    (∑ go : Polynomial params × Outcome,
        (∑ _u : Unit,
            leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ *
          (∑ _u : Unit,
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
              (∑ _u : Unit,
                  leftTensor (ι₂ := ι)
                    (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))ᴴ *
                (∑ _u : Unit,
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

/-- The left-front explicit scalar appearing in the final `sqrt chi` switcheroo step. -/
noncomputable def switcherooLeftFrontCoreScalar
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
    ∑ go : Polynomial params × Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          (((family.meas q.1).outcome go.1) *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1 *
            (M q.2).outcome go.2)))

/-- The split-by-`g` scalar that collapses to the first positive switcheroo term. -/
noncomputable def switcherooFirstSplitCoreScalar
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
    ∑ go : Polynomial params × Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1 *
            (M q.2).outcome go.2)))

/-- Normalize the pointwise self-product in the final switcheroo left-front
step to the split-by-`g` scalar. -/
lemma switcherooPointProductLeft_self_eq_firstSplit_point
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (go : Polynomial params × Outcome) :
    ev ψbi
      (((switcherooPointProductLeft params family M q).outcome go)ᴴ *
        (switcherooPointProductLeft params family M q).outcome go) =
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1 *
            (M q.2).outcome go.2)) := by
  let G : MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome go.1
  let Mo : MIPStarRE.Quantum.Op ι := (M q.2).outcome go.2
  have hGherm : Gᴴ = G := (family.meas q.1).outcome_hermitian go.1
  have hMoherm : Moᴴ = Mo := (M q.2).outcome_hermitian go.2
  calc
    ev ψbi
        (((switcherooPointProductLeft params family M q).outcome go)ᴴ *
          (switcherooPointProductLeft params family M q).outcome go)
      = ev ψbi ((leftTensor (ι₂ := ι) (G * Mo))ᴴ * leftTensor (ι₂ := ι) (G * Mo)) := by
          simp [switcherooPointProductLeft, orderedProductOpFamily,
            OpFamily.leftPlacedOpFamily, G, Mo]
    _ = ev ψbi (leftTensor (ι₂ := ι) (((G * Mo)ᴴ) * (G * Mo))) := by
          rw [show (leftTensor (ι₂ := ι) (G * Mo))ᴴ =
              leftTensor (ι₂ := ι) ((G * Mo)ᴴ) by
                simpa [leftTensor, opTensor] using
                  (conjTranspose_opTensor (G * Mo) (1 : MIPStarRE.Quantum.Op ι))]
          rw [leftTensor_mul_leftTensor]
    _ = ev ψbi (leftTensor (ι₂ := ι) (Mo * G * G * Mo)) := by
          congr 1
          simp [Matrix.conjTranspose_mul, hGherm, hMoherm, mul_assoc]
    _ = ev ψbi (leftTensor (ι₂ := ι) (Mo * G * Mo)) := by
          have hcollapse : Mo * G * G * Mo = Mo * G * Mo := by
            calc
              Mo * G * G * Mo = Mo * (G * G) * Mo := by simp [mul_assoc]
              _ = Mo * G * Mo := by rw [(family.meas q.1).proj go.1]
          exact congrArg (fun X => ev ψbi (leftTensor (ι₂ := ι) X)) hcollapse
    _ = ev ψbi
          (leftTensor (ι₂ := ι)
            ((M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2)) := by
          simp [G, Mo]

/-- Normalize the pointwise mixed product in the final switcheroo left-front step
into the left-front scalar form. -/
lemma switcherooPointProductRightLeft_eq_leftFront_point
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (go : Polynomial params × Outcome) :
    ev ψbi
      (((switcherooPointProductRight params family M q).outcome go)ᴴ *
        (switcherooPointProductLeft params family M q).outcome go) =
      ev ψbi
        (leftTensor (ι₂ := ι)
          (((family.meas q.1).outcome go.1) *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1 *
            (M q.2).outcome go.2)) := by
  let G : MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome go.1
  let Mo : MIPStarRE.Quantum.Op ι := (M q.2).outcome go.2
  have hGherm : Gᴴ = G := (family.meas q.1).outcome_hermitian go.1
  have hMoherm : Moᴴ = Mo := (M q.2).outcome_hermitian go.2
  calc
    ev ψbi
        (((switcherooPointProductRight params family M q).outcome go)ᴴ *
          (switcherooPointProductLeft params family M q).outcome go)
      = ev ψbi ((leftTensor (ι₂ := ι) (Mo * G))ᴴ * leftTensor (ι₂ := ι) (G * Mo)) := by
          simp [switcherooPointProductLeft, switcherooPointProductRight,
            orderedProductOpFamily, reversedProductOpFamily,
            OpFamily.leftPlacedOpFamily, G, Mo]
    _ = ev ψbi (leftTensor (ι₂ := ι) (((Mo * G)ᴴ) * (G * Mo))) := by
          rw [show (leftTensor (ι₂ := ι) (Mo * G))ᴴ =
              leftTensor (ι₂ := ι) ((Mo * G)ᴴ) by
                simpa [leftTensor, opTensor] using
                  (conjTranspose_opTensor (Mo * G) (1 : MIPStarRE.Quantum.Op ι))]
          rw [leftTensor_mul_leftTensor]
    _ = ev ψbi (leftTensor (ι₂ := ι) (G * Mo * G * Mo)) := by
          congr 1
          simp [Matrix.conjTranspose_mul, hGherm, hMoherm, mul_assoc]
    _ = ev ψbi
          (leftTensor (ι₂ := ι)
            (((family.meas q.1).outcome go.1) *
              (M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2)) := by
          simp [G, Mo]

/-- Average the single-question four-term `qSDDOp` expansion over the
slice-pair distribution. -/
lemma switcherooAggregate_qSDDOp_expand_avg
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
  let 𝒟q : Distribution (SlicePairQuestion params) :=
    uniformDistribution (SlicePairQuestion params)
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
  have hA :
      avgOver 𝒟q A = switcherooAggregateFirstTerm params ψbi family M := by
    rfl
  have hB :
      avgOver 𝒟q B = switcherooAggregateSecondTerm params ψbi family M := by
    rfl
  have hC :
      avgOver 𝒟q C = switcherooAggregateThirdTerm params ψbi family M := by
    rfl
  have hD :
      avgOver 𝒟q D = switcherooAggregateFourthTerm params ψbi family M := by
    rfl
  change avgOver 𝒟q
      (fun q => qSDDOp ψbi
        (switcherooAggregateLeft params family M q)
        (switcherooAggregateRight params family M q)) = _
  calc
    avgOver 𝒟q
        (fun q => qSDDOp ψbi
          (switcherooAggregateLeft params family M q)
          (switcherooAggregateRight params family M q))
      = avgOver 𝒟q (fun q => A q + B q - C q - D q) := by
          apply avgOver_congr
          intro q
          rw [switcherooAggregate_qSDDOp_expand]
          simp [A, B, C, D, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = avgOver 𝒟q A + avgOver 𝒟q B - avgOver 𝒟q C - avgOver 𝒟q D := by
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
          rw [hA, hB, hC, hD]

end MIPStarRE.LDT.Pasting
