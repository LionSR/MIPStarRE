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

end MIPStarRE.LDT.Pasting
