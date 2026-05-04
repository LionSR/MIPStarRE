import MIPStarRE.LDT.Pasting.SwitcherooSetup.Centers

/-!
# Section 12 pasting: switcheroo aggregate terms

The remaining switcheroo aggregate terms and split formulas.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The one-outcome projective family whose sole effect is the complete slice part `G^x`. -/
noncomputable def completePartProjFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (SliceQuestion params) Unit ι :=
  fun x =>
    { toSubMeas := completePartSubMeas params family x
      proj := by
        intro u
        cases u
        rw [completePartSubMeas_outcome_unit params family x]
        simpa using ProjSubMeas.total_proj (family.meas x) }

/-- The second positive term in the switcheroo expansion. -/
noncomputable def switcherooAggregateSecondTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total * (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))

/-- The third (negative) term in the switcheroo expansion. -/
noncomputable def switcherooAggregateThirdTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total))

/-- The fourth (negative) term in the switcheroo expansion. -/
noncomputable def switcherooAggregateFourthTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) fun q =>
    ∑ o : Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (completePartSubMeas params family q.1).total *
            (M q.2).outcome o))

lemma switcherooAggregateThirdTerm_eq_fourthTerm
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooAggregateThirdTerm params ψbi family M =
      switcherooAggregateFourthTerm params ψbi family M := by
  unfold switcherooAggregateThirdTerm switcherooAggregateFourthTerm
  apply avgOver_congr
  intro q
  refine Finset.sum_congr rfl ?_
  intro o _
  let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family q.1).total
  let Mo : MIPStarRE.Quantum.Op ι := (M q.2).outcome o
  have hGherm : Gᴴ = G :=
    (Matrix.nonneg_iff_posSemidef.mp
      (SubMeas.total_nonneg (completePartSubMeas params family q.1))).isHermitian.eq
  have hMoherm : Moᴴ = Mo :=
    (Matrix.nonneg_iff_posSemidef.mp ((M q.2).outcome_pos o)).isHermitian.eq
  calc
    ev ψbi (leftTensor (ι₂ := ι) (Mo * G * Mo * G))
      = ev ψbi ((leftTensor (ι₂ := ι) (Mo * G * Mo * G))ᴴ) := by
          symm
          exact ev_conjTranspose ψbi _
    _ = ev ψbi (leftTensor (ι₂ := ι) ((Mo * G * Mo * G)ᴴ)) := by
          congr 1
          simpa [leftTensor, opTensor] using
            (conjTranspose_opTensor (Mo * G * Mo * G)
              (1 : MIPStarRE.Quantum.Op ι))
    _ = ev ψbi (leftTensor (ι₂ := ι) (G * Mo * G * Mo)) := by
          congr 1
          simp [mul_assoc, Matrix.conjTranspose_mul, hGherm, hMoherm]

/-- Split the fourth switcheroo term by inserting the complete-part projector
resolution `G = ∑_g G_g`. -/
lemma switcherooAggregateFourthTerm_eq_split
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooAggregateFourthTerm params ψbi family M =
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ go : Polynomial params × Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2))) := by
  unfold switcherooAggregateFourthTerm
  apply avgOver_congr
  intro q
  let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family q.1).total
  let Gq : Polynomial params → MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome
  calc
    ∑ o : Outcome,
        ev ψbi
          (leftTensor (ι₂ := ι)
            (G * (M q.2).outcome o * G * (M q.2).outcome o))
      = ∑ o : Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι)
              (G * (M q.2).outcome o * (∑ g : Polynomial params, Gq g) *
                (M q.2).outcome o)) := by
            refine Finset.sum_congr rfl ?_
            intro o _
            rw [(family.meas q.1).sum_eq_total]
            simp [G]
    _ = ∑ o : Outcome,
          ∑ g : Polynomial params,
            ev ψbi
              (leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * (M q.2).outcome o)) := by
            refine Finset.sum_congr rfl ?_
            intro o _
            rw [← ev_sum ψbi (fun g : Polynomial params =>
              leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * (M q.2).outcome o))]
            congr 1
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ,
              Matrix.mul_sum, Finset.sum_mul]
    _ = ∑ o : Outcome,
          ∑ g : Polynomial params,
            ev ψbi
              (leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * Gq g * (M q.2).outcome o)) := by
            refine Finset.sum_congr rfl ?_
            intro o _
            refine Finset.sum_congr rfl ?_
            intro g _
            simp [Gq, mul_assoc, (family.meas q.1).proj g]
    _ = ∑ g : Polynomial params,
          ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι)
                (G * (M q.2).outcome o * Gq g * Gq g * (M q.2).outcome o)) := by
            rw [Finset.sum_comm]
    _ = ∑ go : Polynomial params × Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι)
              (G * (M q.2).outcome go.2 * Gq go.1 * Gq go.1 * (M q.2).outcome go.2)) := by
            symm
            simpa using
              (Fintype.sum_prod_type' (f := fun g o =>
                ev ψbi
                  (leftTensor (ι₂ := ι)
                    (G * (M q.2).outcome o * Gq g * Gq g * (M q.2).outcome o))))

end MIPStarRE.LDT.Pasting
