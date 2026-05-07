import MIPStarRE.LDT.Pasting.SwitcherooContraction.Split

/-!
# Section 12 pasting: switcheroo commuted contraction

The once-commuted contraction steps and the split-by-`g` rewrite.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Right-action contraction witness for the second `sqrt zeta` transfer. -/
lemma switcherooAggregateFourthTerm_once_commuted_contraction_right
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    (∑ g : Polynomial params,
        (∑ o : Outcome,
            leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))ᴴ *
          (∑ o : Outcome,
            leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))) ≤ 1 := by
  let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family q.1).total
  let Gq : Polynomial params → MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome
  let Mo : Outcome → MIPStarRE.Quantum.Op ι := (M q.2).outcome
  let X : Polynomial params → MIPStarRE.Quantum.Op ι :=
    switcherooAggregateFourthTermX params family M q
  have hGherm : Gᴴ = G := by
    simpa [G] using switcherooCompletePartTotal_hermitian params family q
  have hGsq : G * G = G := by
    simpa [G] using switcherooCompletePartTotal_sq params family q
  have hGle : G ≤ 1 := by
    simpa [G] using switcherooCompletePartTotal_le_one params family q
  have hMoherm : ∀ o : Outcome, (Mo o)ᴴ = Mo o := by
    intro o
    simpa [Mo] using switcherooMeasuredOutcome_hermitian params M q o
  have hGqherm : ∀ g : Polynomial params, (Gq g)ᴴ = Gq g := by
    intro g
    simpa [Gq] using switcherooSliceOutcome_hermitian params family q g
  have hXherm : ∀ g : Polynomial params, (X g)ᴴ = X g := by
    intro g
    simpa [X] using switcherooAggregateFourthTermX_hermitian params family M q g
  have hXnonneg : ∀ g : Polynomial params, 0 ≤ X g := by
    intro g
    simpa [X] using switcherooAggregateFourthTermX_nonneg params family M q g
  have hXle : ∀ g : Polynomial params, X g ≤ 1 := by
    intro g
    simpa [X] using switcherooAggregateFourthTermX_le_one params family M q g
  have hXsq_le : ∀ g : Polynomial params, X g * X g ≤ X g := by
    intro g
    simpa [X] using switcherooAggregateFourthTermX_sq_le params family M q g
  have hsumX : ∑ g : Polynomial params, X g = ∑ o : Outcome, Mo o * G * Mo o := by
    simpa [X, G, Mo] using switcherooAggregateFourthTermX_sum params family M q
  have hmid_le : ∑ o : Outcome, Mo o * G * Mo o ≤ 1 := by
    simpa [G, Mo] using switcherooAggregateFourthTerm_middle_sum_le_one params family M q
  have hsingle :
      ∀ g : Polynomial params,
        (∑ o : Outcome,
            leftTensor (ι₂ := ι)
              (G * Mo o * Gq g * Mo o))ᴴ *
          (∑ o : Outcome,
            leftTensor (ι₂ := ι)
              (G * Mo o * Gq g * Mo o)) ≤
            leftTensor (ι₂ := ι) (X g) := by
    intro g
    calc
      (∑ o : Outcome, leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o))ᴴ *
          (∑ o : Outcome, leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o))
        = leftTensor (ι₂ := ι) (X g * G * X g) := by
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun o : Outcome => G * Mo o * Gq g * Mo o)]
            calc
              (leftTensor (ι₂ := ι) (∑ o : Outcome, G * Mo o * Gq g * Mo o))ᴴ *
                  leftTensor (ι₂ := ι) (∑ o : Outcome, G * Mo o * Gq g * Mo o)
                = leftTensor (ι₂ := ι) ((∑ o : Outcome, G * Mo o * Gq g * Mo o)ᴴ) *
                    leftTensor (ι₂ := ι) (∑ o : Outcome, G * Mo o * Gq g * Mo o) := by
                      congr 2
                      simpa [leftTensor, opTensor] using
                        (conjTranspose_opTensor
                          (∑ o : Outcome, G * Mo o * Gq g * Mo o)
                          (1 : MIPStarRE.Quantum.Op ι))
              _ = leftTensor (ι₂ := ι)
                    (((∑ o : Outcome, G * Mo o * Gq g * Mo o)ᴴ) *
                      (∑ o : Outcome, G * Mo o * Gq g * Mo o)) := by
                      rw [leftTensor_mul_leftTensor]
              _ = leftTensor (ι₂ := ι) (X g * G * X g) := by
                      congr 1
                      rw [show (∑ o : Outcome, G * Mo o * Gq g * Mo o) = G * X g by
                        simpa [X, switcherooAggregateFourthTermX, mul_assoc] using
                          (Finset.mul_sum (s := Finset.univ) (a := G)
                            (f := fun o : Outcome => Mo o * Gq g * Mo o)).symm]
                      calc
                        (G * X g)ᴴ * (G * X g)
                          = (X g * G) * (G * X g) := by
                              simp [Matrix.conjTranspose_mul, hGherm, hXherm g]
                        _ = X g * (G * G) * X g := by simp [mul_assoc]
                        _ = X g * G * X g := by rw [hGsq]
      _ ≤ leftTensor (ι₂ := ι) (X g * X g) := by
            simpa [leftTensor, opTensor, mul_assoc] using
              (opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
                (MIPStarRE.Quantum.sandwich_mono (hXherm g) hGle)
                (show (0 : MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one))
      _ ≤ leftTensor (ι₂ := ι) (X g) := by
            simpa [leftTensor, opTensor] using
              (opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
                (hXsq_le g) (show (0 : MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one))
  calc
    (∑ g : Polynomial params,
        (∑ o : Outcome,
            leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))ᴴ *
          (∑ o : Outcome,
            leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o)))
      ≤ ∑ g : Polynomial params, leftTensor (ι₂ := ι) (X g) := by
          refine Finset.sum_le_sum ?_
          intro g _
          simpa [G, Gq, Mo] using hsingle g
    _ = leftTensor (ι₂ := ι) (∑ g : Polynomial params, X g) := by
          rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun g : Polynomial params => X g)]
    _ ≤ 1 := by
          calc
            leftTensor (ι₂ := ι) (∑ g : Polynomial params, X g)
              = leftTensor (ι₂ := ι) (∑ o : Outcome, Mo o * G * Mo o) := by rw [hsumX]
            _ ≤ leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) := by
                simpa [leftTensor, opTensor] using
                  (opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
                    hmid_le (show (0 : MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one))
            _ = 1 := by simp [leftTensor]

/-- Collapse the split-by-`g` raw expression back to the first positive
switcheroo term. -/
lemma switcherooAggregateFirstTerm_eq_split_by_g
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
      ∑ go : Polynomial params × Outcome,
        ev ψbi
          (leftTensor (ι₂ := ι)
            ((M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2))) =
      switcherooAggregateFirstTerm params ψbi family M := by
  calc
    avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
      ∑ go : Polynomial params × Outcome,
        ev ψbi
          (leftTensor (ι₂ := ι)
            ((M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2)))
      = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((M q.2).outcome o *
                  (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o))) := by
            apply avgOver_congr
            intro q
            calc
              ∑ go : Polynomial params × Outcome,
                  ev ψbi
                    (leftTensor (ι₂ := ι)
                      ((M q.2).outcome go.2 *
                        (family.meas q.1).outcome go.1 *
                        (M q.2).outcome go.2))
                = ∑ g : Polynomial params,
                    ∑ o : Outcome,
                      ev ψbi
                        (leftTensor (ι₂ := ι)
                          ((M q.2).outcome o *
                            (family.meas q.1).outcome g *
                            (M q.2).outcome o)) := by
                      simpa using
                        (Fintype.sum_prod_type' (f := fun g o =>
                          ev ψbi
                            (leftTensor (ι₂ := ι)
                              ((M q.2).outcome o *
                                (family.meas q.1).outcome g *
                                (M q.2).outcome o))))
              _ = ∑ o : Outcome,
                    ∑ g : Polynomial params,
                      ev ψbi
                        (leftTensor (ι₂ := ι)
                          ((M q.2).outcome o *
                            (family.meas q.1).outcome g *
                            (M q.2).outcome o)) := by
                      rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro o _
            calc
              ∑ g : Polynomial params,
                  ev ψbi
                    (leftTensor (ι₂ := ι)
                      ((M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o))
                = ev ψbi
                    (∑ g : Polynomial params,
                      leftTensor (ι₂ := ι)
                        ((M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o)) := by
                    rw [← ev_sum ψbi]
              _ = ev ψbi
                    (leftTensor (ι₂ := ι)
                      (∑ g : Polynomial params,
                        (M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o)) := by
                    rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ]
              _ = ev ψbi
                    (leftTensor (ι₂ := ι)
                      ((M q.2).outcome o * (∑ g : Polynomial params, (family.meas q.1).outcome g) *
                        (M q.2).outcome o)) := by
                    congr 1
                    simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
              _ = ev ψbi
                    (leftTensor (ι₂ := ι)
                      ((M q.2).outcome o * (completePartSubMeas params family q.1).total *
                        (M q.2).outcome o)) := by
                    rw [(family.meas q.1).sum_eq_total]
                    simp [completePartSubMeas, postprocess_total]
    _ = switcherooAggregateFirstTerm params ψbi family M := by
          unfold switcherooAggregateFirstTerm
          rfl

end MIPStarRE.LDT.Pasting
