import MIPStarRE.LDT.Pasting.SwitcherooContraction
import MIPStarRE.LDT.Pasting.SwitcherooCompletion.Expansion

/-!
# Section 12 pasting: fourth-term chain helpers

Private helpers for the fourth-term chain in `commutativitySwitcheroo`.
These were extracted from `SwitcherooCompletion` to keep that file under
the 1000-line threshold.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

lemma switcherooAggregateLeftFrontRaw_point
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    (∑ go : Polynomial params × Outcome,
        ∑ _u : Unit,
          ev ψbi
            ((switcherooPointProductLeft params family M q).outcome go *
              leftTensor (ι₂ := ι)
                (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))) =
      ∑ go : Polynomial params × Outcome,
        ev ψbi
          (leftTensor (ι₂ := ι)
            (((family.meas q.1).outcome go.1) *
              (M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2)) := by
  refine Finset.sum_congr rfl ?_
  intro go _
  rcases go with ⟨g, o⟩
  simp [switcherooPointProductLeft, orderedProductOpFamily,
    OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc]

lemma switcherooAggregateFirstSplitRaw_point
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    (∑ go : Polynomial params × Outcome,
        ∑ _u : Unit,
          ev ψbi
            ((switcherooPointProductRight params family M q).outcome go *
              leftTensor (ι₂ := ι)
                (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2))) =
      ∑ go : Polynomial params × Outcome,
        ev ψbi
          (leftTensor (ι₂ := ι)
            ((M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2)) := by
  refine Finset.sum_congr rfl ?_
  intro go _
  rcases go with ⟨g, o⟩
  calc
    ∑ u : Unit,
        ev ψbi
          ((switcherooPointProductRight params family M q).outcome (g, o) *
            leftTensor (ι₂ := ι) (((family.meas q.1).outcome g) * (M q.2).outcome o))
      = ev ψbi
          (leftTensor (ι₂ := ι)
            ((M q.2).outcome o * (family.meas q.1).outcome g *
              (family.meas q.1).outcome g * (M q.2).outcome o)) := by
              simp [switcherooPointProductRight, reversedProductOpFamily,
                OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc]
    _ = ev ψbi
          (leftTensor (ι₂ := ι)
            ((M q.2).outcome o * (family.meas q.1).outcome g *
              (M q.2).outcome o)) := by
              congr 1
              simp [mul_assoc, (family.meas q.1).proj g]

lemma switcherooAggregateMixedRaw_point
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    (∑ g : Polynomial params, ∑ o : Outcome,
        ev ψbi
          (rightTensor (ι₁ := ι) ((family.meas q.1).outcome g) *
            leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))) =
      ∑ g : Polynomial params, ∑ o : Outcome,
        ev ψbi
          ((leftTensor (ι₂ := ι)
            ((completePartSubMeas params family q.1).total *
              (M q.2).outcome o *
              (family.meas q.1).outcome g *
              (M q.2).outcome o)) *
            rightTensor (ι₁ := ι) ((family.meas q.1).outcome g)) := by
  refine Finset.sum_congr rfl ?_
  intro g _
  refine Finset.sum_congr rfl ?_
  intro o _
  rw [rightTensor_mul_leftTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
lemma switcherooAggregateMixedRaw_close_leftFrontRaw
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    |switcherooAggregateMixedRaw params ψbi family M -
        switcherooAggregateLeftFrontRaw params ψbi family M| ≤ Real.sqrt zeta := by
  have hleft :
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ g : Polynomial params, ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι) ((family.meas q.1).outcome g) *
                leftTensor (ι₂ := ι)
                  ((completePartSubMeas params family q.1).total *
                    (M q.2).outcome o *
                    (family.meas q.1).outcome g *
                    (M q.2).outcome o))) =
        switcherooAggregateLeftFrontRaw params ψbi family M := by
    unfold switcherooAggregateLeftFrontRaw
    apply avgOver_congr
    intro q
    calc
      ∑ g : Polynomial params, ∑ o : Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι) ((family.meas q.1).outcome g) *
              leftTensor (ι₂ := ι)
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (family.meas q.1).outcome g *
                  (M q.2).outcome o))
        = ∑ g : Polynomial params, ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((family.meas q.1).outcome g *
                  (M q.2).outcome o *
                  (family.meas q.1).outcome g *
                  (M q.2).outcome o)) := by
              refine Finset.sum_congr rfl ?_
              intro g _
              refine Finset.sum_congr rfl ?_
              intro o _
              have htotal :
                  (completePartSubMeas params family q.1).total = (family.meas q.1).total := by
                simp [completePartSubMeas, postprocess_total]
              calc
                ev ψbi
                    (leftTensor (ι₂ := ι) ((family.meas q.1).outcome g) *
                      leftTensor (ι₂ := ι)
                        ((completePartSubMeas params family q.1).total *
                          (M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o))
                  = ev ψbi
                      (leftTensor (ι₂ := ι)
                        ((family.meas q.1).outcome g *
                          (completePartSubMeas params family q.1).total *
                          (M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o)) := by
                            simp [leftTensor_mul_leftTensor, mul_assoc]
                _ = ev ψbi
                      (leftTensor (ι₂ := ι)
                        (((family.meas q.1).outcome g * (family.meas q.1).total) *
                          (M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o)) := by
                            rw [htotal]
                _ = ev ψbi
                      (leftTensor (ι₂ := ι)
                        ((family.meas q.1).outcome g *
                          (M q.2).outcome o *
                          (family.meas q.1).outcome g *
                          (M q.2).outcome o)) := by
                            rw [Preliminaries.projSubMeas_outcome_mul_total_eq_outcome
                              (family.meas q.1) g]
      _ = ∑ go : Polynomial params × Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((family.meas q.1).outcome go.1 *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1 *
                  (M q.2).outcome go.2)) := by
              let f : Polynomial params → Outcome → Error := fun g o =>
                ev ψbi
                  (leftTensor (ι₂ := ι)
                    ((family.meas q.1).outcome g *
                      (M q.2).outcome o *
                      (family.meas q.1).outcome g *
                      (M q.2).outcome o))
              change (∑ g : Polynomial params, ∑ o : Outcome, f g o) =
                ∑ go : Polynomial params × Outcome, f go.1 go.2
              simpa using (Fintype.sum_prod_type' (f := f)).symm
  have hright :
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ g : Polynomial params, ∑ o : Outcome,
            ev ψbi
              (rightTensor (ι₁ := ι) ((family.meas q.1).outcome g) *
                leftTensor (ι₂ := ι)
                  ((completePartSubMeas params family q.1).total *
                    (M q.2).outcome o *
                    (family.meas q.1).outcome g *
                    (M q.2).outcome o))) =
        switcherooAggregateMixedRaw params ψbi family M := by
    unfold switcherooAggregateMixedRaw
    apply avgOver_congr
    intro q
    simpa [switcherooAggregateMixedRaw] using
      switcherooAggregateMixedRaw_point params ψbi family M q
  calc
    |switcherooAggregateMixedRaw params ψbi family M -
        switcherooAggregateLeftFrontRaw params ψbi family M|
      = |avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
            ∑ g : Polynomial params, ∑ o : Outcome,
              ev ψbi
                (leftTensor (ι₂ := ι) ((family.meas q.1).outcome g) *
                  leftTensor (ι₂ := ι)
                    ((completePartSubMeas params family q.1).total *
                      (M q.2).outcome o *
                      (family.meas q.1).outcome g *
                      (M q.2).outcome o))) -
          avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
            ∑ g : Polynomial params, ∑ o : Outcome,
              ev ψbi
                (rightTensor (ι₁ := ι) ((family.meas q.1).outcome g) *
                  leftTensor (ι₂ := ι)
                    ((completePartSubMeas params family q.1).total *
                      (M q.2).outcome o *
                      (family.meas q.1).outcome g *
                      (M q.2).outcome o)))| := by
            rw [hleft, hright, abs_sub_comm]
    _ ≤ Real.sqrt zeta :=
      switcherooAggregateFourthTerm_mixed_close_left_front_raw
          params ψbi hnorm family M zeta hselfG

lemma switcherooAggregateOnceCommutedRaw_point
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    (∑ g : Polynomial params, ∑ o : Outcome,
        ev ψbi
          (leftTensor (ι₂ := ι)
            ((completePartSubMeas params family q.1).total *
              (M q.2).outcome o *
              (family.meas q.1).outcome g *
              (M q.2).outcome o *
              (family.meas q.1).outcome g))) =
      ∑ go : Polynomial params × Outcome,
        ev ψbi
          (leftTensor (ι₂ := ι)
            ((completePartSubMeas params family q.1).total *
              (M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2 *
              (family.meas q.1).outcome go.1)) := by
  let f : Polynomial params → Outcome → Error := fun g o =>
    ev ψbi
      (leftTensor (ι₂ := ι)
        ((completePartSubMeas params family q.1).total *
          (M q.2).outcome o *
          (family.meas q.1).outcome g *
          (M q.2).outcome o *
          (family.meas q.1).outcome g))
  change (∑ g : Polynomial params, ∑ o : Outcome, f g o) =
    ∑ go : Polynomial params × Outcome, f go.1 go.2
  simpa using (Fintype.sum_prod_type' (f := f)).symm
lemma switcherooAggregateOnceCommutedRaw_close_mixed
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    |switcherooAggregateOnceCommutedRaw params ψbi family M -
        switcherooAggregateMixedRaw params ψbi family M| ≤ Real.sqrt zeta := by
  have hleft :
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ g : Polynomial params, ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (family.meas q.1).outcome g *
                  (M q.2).outcome o *
                  (family.meas q.1).outcome g))) =
        switcherooAggregateOnceCommutedRaw params ψbi family M := by
    change avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ g : Polynomial params, ∑ o : Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o *
                (family.meas q.1).outcome g))) =
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ go : Polynomial params × Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1)))
    apply avgOver_congr
    intro q
    exact switcherooAggregateOnceCommutedRaw_point params ψbi family M q
  have hright :
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ g : Polynomial params, ∑ o : Outcome,
            ev ψbi
              ((leftTensor (ι₂ := ι)
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (family.meas q.1).outcome g *
                    (M q.2).outcome o)) *
                rightTensor (ι₁ := ι) ((family.meas q.1).outcome g))) =
        switcherooAggregateMixedRaw params ψbi family M := by
    rfl
  calc
    |switcherooAggregateOnceCommutedRaw params ψbi family M -
        switcherooAggregateMixedRaw params ψbi family M|
      = |avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
            ∑ g : Polynomial params, ∑ o : Outcome,
              ev ψbi
                (leftTensor (ι₂ := ι)
                  ((completePartSubMeas params family q.1).total *
                    (M q.2).outcome o *
                    (family.meas q.1).outcome g *
                    (M q.2).outcome o *
                    (family.meas q.1).outcome g))) -
          avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
            ∑ g : Polynomial params, ∑ o : Outcome,
              ev ψbi
                ((leftTensor (ι₂ := ι)
                  ((completePartSubMeas params family q.1).total *
                    (M q.2).outcome o *
                    (family.meas q.1).outcome g *
                    (M q.2).outcome o)) *
                  rightTensor (ι₁ := ι) ((family.meas q.1).outcome g)))| := by
            rw [hleft, hright]
    _ ≤ Real.sqrt zeta :=
        switcherooAggregateFourthTerm_once_commuted_close_mixed
          params ψbi hnorm family M zeta hselfG

-- The last `χ`-step needs only pointwise normalization for the raw `G_g M_o`
-- factors inside `closenessOfInnerProduct_right`; the heavy adjoint rewrites are
-- isolated in the two pointwise helper lemmas above.
/-- The final `sqrt chi` bridge in the fourth-term chain: compare the left-front
raw scalar with the split-by-`g` scalar that later collapses to the first
positive switcheroo term. -/
lemma switcherooAggregateLeftFrontRaw_close_firstSplitRaw
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (chi : Error)
    (hcomm : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (switcherooPointProductLeft params family M)
      (switcherooPointProductRight params family M)
      chi) :
    |switcherooAggregateLeftFrontRaw params ψbi family M -
        switcherooAggregateFirstSplitRaw params ψbi family M| ≤
      Real.sqrt chi := by
  let 𝒟q : Distribution (SlicePairQuestion params) :=
    uniformDistribution (SlicePairQuestion params)
  let A : SlicePairQuestion params → Polynomial params × Outcome → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go => ((switcherooPointProductLeft params family M q).outcome go)ᴴ
  let B : SlicePairQuestion params → Polynomial params × Outcome → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go => ((switcherooPointProductRight params family M q).outcome go)ᴴ
  let C : SlicePairQuestion params → Polynomial params × Outcome → Unit →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go () => (switcherooPointProductLeft params family M q).outcome go
  have h𝒟q : ∑ q ∈ 𝒟q.support, 𝒟q.weight q ≤ 1 := by
    simpa [𝒟q] using uniformDistribution_weight_sum_le_one (SlicePairQuestion params)
  have hAB :
      avgOver 𝒟q
        (fun q => qSDDCore ψbi (fun go => (A q go)ᴴ) (fun go => (B q go)ᴴ)) ≤ chi := by
    simpa [𝒟q, A, B] using
      switcherooPointProductCommutation_coreBound params ψbi family M chi hcomm
  have hC :
      ∀ q,
        (∑ go : Polynomial params × Outcome,
            (∑ u : Unit, C q go u)ᴴ * (∑ u : Unit, C q go u)) ≤ 1 := by
    intro q
    simpa [C, switcherooPointProductLeft, orderedProductOpFamily,
        OpFamily.leftPlacedOpFamily] using
      switcherooAggregateLeftFront_contraction params family M q
  have hleft :
      avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome,
            ∑ b : Unit, ev ψbi (A q a * C q a b)) =
        switcherooAggregateFirstSplitRaw params ψbi family M := by
    unfold switcherooAggregateFirstSplitRaw
    apply avgOver_congr
    intro q
    refine Finset.sum_congr rfl ?_
    intro go _
    calc
      ∑ b : Unit, ev ψbi (A q go * C q go b)
        = ev ψbi (A q go * C q go ()) := by simp
      _ = ev ψbi
            (leftTensor (ι₂ := ι)
              ((M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2)) := by
            simpa [A, C] using
              switcherooPointProductLeft_self_eq_firstSplit_point
                (params := params) (ψbi := ψbi) (family := family) (M := M) q go
      _ = ev ψbi
            (leftTensor (ι₂ := ι)
              ((M q.2).outcome go.2 *
                ((family.meas q.1).outcome go.1 * (M q.2).outcome go.2))) := by
            simp [mul_assoc]
  have hright :
      avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome,
            ∑ b : Unit, ev ψbi (B q a * C q a b)) =
        switcherooAggregateLeftFrontRaw params ψbi family M := by
    unfold switcherooAggregateLeftFrontRaw
    apply avgOver_congr
    intro q
    refine Finset.sum_congr rfl ?_
    intro go _
    calc
      ∑ b : Unit, ev ψbi (B q go * C q go b)
        = ev ψbi (B q go * C q go ()) := by simp
      _ = ev ψbi
            (leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2)) := by
            simpa [B, C] using
              switcherooPointProductRightLeft_eq_leftFront_point
                (params := params) (ψbi := ψbi) (family := family) (M := M) q go
  have hleft' :
      avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome, ev ψbi (A q a * C q a ())) =
        switcherooAggregateFirstSplitRaw params ψbi family M := by
    simpa using hleft
  have hright' :
      avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome, ev ψbi (B q a * C q a ())) =
        switcherooAggregateLeftFrontRaw params ψbi family M := by
    simpa using hright
  have hclose :=
    Preliminaries.closenessOfInnerProduct_right ψbi hnorm 𝒟q h𝒟q A B C chi hAB hC
  have hclose' :
      |avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome, ev ψbi (A q a * C q a ())) -
        avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome, ev ψbi (B q a * C q a ()))| ≤
        Real.sqrt chi := by
    simpa using hclose
  simpa [hleft', hright', abs_sub_comm] using hclose'

end MIPStarRE.LDT.Pasting
