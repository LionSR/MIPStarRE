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
    fun g => ∑ o : Outcome, Mo o * Gq g * Mo o
  have hGherm : Gᴴ = G :=
    (Matrix.nonneg_iff_posSemidef.mp
      (SubMeas.total_nonneg (completePartSubMeas params family q.1))).isHermitian.eq
  have hGsq : G * G = G := by
    simpa [G, completePartSubMeas, postprocess_total] using
      projSubMeas_total_sq (family.meas q.1)
  have hGle : G ≤ 1 := by
    simpa [G] using (completePartSubMeas params family q.1).total_le_one
  have hMoherm : ∀ o : Outcome, (Mo o)ᴴ = Mo o := by
    intro o
    exact (Matrix.nonneg_iff_posSemidef.mp ((M q.2).outcome_pos o)).isHermitian.eq
  have hGqherm : ∀ g : Polynomial params, (Gq g)ᴴ = Gq g := by
    intro g
    exact (Matrix.nonneg_iff_posSemidef.mp ((family.meas q.1).outcome_pos g)).isHermitian.eq
  have hXherm : ∀ g : Polynomial params, (X g)ᴴ = X g := by
    intro g
    unfold X
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl ?_
    intro o _
    simp [Matrix.conjTranspose_mul, hMoherm o, hGqherm g, mul_assoc]
  have hXnonneg : ∀ g : Polynomial params, 0 ≤ X g := by
    intro g
    unfold X
    refine Finset.sum_nonneg ?_
    intro o _
    exact MIPStarRE.Quantum.sandwich_nonneg ((family.meas q.1).outcome_pos g) (hMoherm o)
  have hXle : ∀ g : Polynomial params, X g ≤ 1 := by
    intro g
    exact projSubMeas_sandwich_sum_le_one (M q.2) (Gq g)
      ((family.meas q.1).outcome_le_one g)
  have hXsq_le : ∀ g : Polynomial params, X g * X g ≤ X g := by
    intro g
    exact MIPStarRE.Quantum.sq_le_self (hXnonneg g) (hXle g)
  have hsumX : ∑ g : Polynomial params, X g = ∑ o : Outcome, Mo o * G * Mo o := by
    unfold X
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro o _
    calc
      ∑ g : Polynomial params, Mo o * Gq g * Mo o
        = Mo o * (∑ g : Polynomial params, Gq g) * Mo o := by
            simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
      _ = Mo o * G * Mo o := by
            rw [(family.meas q.1).sum_eq_total]
            simp [G]
  have hmid_le : ∑ o : Outcome, Mo o * G * Mo o ≤ 1 := by
    exact projSubMeas_sandwich_sum_le_one (M q.2) G hGle
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
                        simp [X, mul_assoc, Matrix.mul_sum]]
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
