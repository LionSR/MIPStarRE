import MIPStarRE.LDT.Pasting.SwitcherooContraction
import MIPStarRE.LDT.Pasting.SwitcherooCompletion.SecondTerm
import MIPStarRE.LDT.Pasting.SwitcherooCompletion.Utilities

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

omit [Fintype ι] [DecidableEq ι] in
private lemma switcheroo_swapDensity_eq_reindex
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity X = Matrix.reindex (Equiv.prodComm ι ι) (Equiv.prodComm ι ι) X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

omit [DecidableEq ι] in
private lemma switcheroo_swapDensity_mul
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (X * Y) = swapDensity X * swapDensity Y := by
  classical
  simpa [switcheroo_swapDensity_eq_reindex] using
    (Matrix.reindexAlgEquiv_mul ℂ ℂ (Equiv.prodComm ι ι) X Y)

private lemma switcheroo_ev_swapDensity_of_density_fixed
    (ψbi : QuantumState (ι × ι))
    (hfix : swapDensity ψbi.density = ψbi.density)
    (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev ψbi (swapDensity Z) = ev ψbi Z := by
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψbi.density * swapDensity Z)
      = MIPStarRE.Quantum.normalizedTrace (swapDensity (ψbi.density * Z)) := by
          rw [switcheroo_swapDensity_mul]
          simp [hfix]
    _ = MIPStarRE.Quantum.normalizedTrace (ψbi.density * Z) :=
          normalizedTrace_swapDensity _

private lemma switcheroo_ev_opTensor_swap
    (ψbi : QuantumState (ι × ι))
    (hfix : swapDensity ψbi.density = ψbi.density)
    (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψbi (opTensor X Y) = ev ψbi (opTensor Y X) := by
  rw [show opTensor Y X = swapDensity (opTensor X Y) by rw [swapDensity_opTensor]]
  exact (switcheroo_ev_swapDensity_of_density_fixed ψbi hfix (opTensor X Y)).symm

/-- Local copy of the first `sqrt zeta` raw fourth-term step so the completion
file can remain self-contained while the split switcheroo modules are still in
flux. -/
private lemma switcherooAggregateFourthTerm_once_commuted_close_mixed_local
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    |avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
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
              rightTensor (ι₁ := ι) ((family.meas q.1).outcome g)))| ≤
      Real.sqrt zeta := by
  let 𝒟q : Distribution (SlicePairQuestion params) :=
    uniformDistribution (SlicePairQuestion params)
  let A : SlicePairQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q g => leftTensor (ι₂ := ι) ((family.meas q.1).outcome g)
  let B : SlicePairQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q g => rightTensor (ι₁ := ι) ((family.meas q.1).outcome g)
  let C : SlicePairQuestion params → Polynomial params → Outcome → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q g o =>
      leftTensor (ι₂ := ι)
        ((completePartSubMeas params family q.1).total *
          (M q.2).outcome o *
          (family.meas q.1).outcome g *
          (M q.2).outcome o)
  have h𝒟q : ∑ q ∈ 𝒟q.support, 𝒟q.weight q ≤ 1 := by
    simpa [𝒟q] using uniformDistribution_weight_sum_le_one (SlicePairQuestion params)
  have hAB : avgOver 𝒟q (fun q => qSDDCore ψbi (A q) (B q)) ≤ zeta := by
    simpa [𝒟q, A, B] using
      switcherooCompletePartSelfConsistency_pairBound params ψbi family zeta hselfG
  have hC :
      ∀ q,
        (∑ g : Polynomial params,
            (∑ o : Outcome, C q g o) * (∑ o : Outcome, C q g o)ᴴ) ≤ 1 := by
    intro q
    simpa [C] using
      switcherooAggregateFourthTerm_once_commuted_contraction_left params family M q
  have hclose :=
    Preliminaries.closenessOfInnerProduct_left ψbi hnorm 𝒟q h𝒟q A B C zeta hAB hC
  simpa [𝒟q, A, B, C, leftTensor_mul_leftTensor, rightTensor_mul_leftTensor_eq_opTensor,
    leftTensor_mul_rightTensor_eq_opTensor, mul_assoc] using hclose

/-- Local copy of the exact split-by-`g` collapse back to the first positive
switcheroo term. -/
private lemma switcherooAggregateFirstTerm_eq_split_by_g_local
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

/-- The named post-second-`sqrt zeta` left-front raw scalar. -/
private noncomputable def switcherooAggregateLeftFrontRawLocal
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

/-- The split-by-`g` raw scalar that collapses to the first positive term. -/
private noncomputable def switcherooAggregateFirstSplitRawLocal
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
            ((family.meas q.1).outcome go.1 *
              (M q.2).outcome go.2))))

/-- The named post-first-`sqrt chi` raw scalar in the fourth-term chain. -/
private noncomputable def switcherooAggregateOnceCommutedRawLocal
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
    ∑ go : Polynomial params × Outcome,
      ev ψbi
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1 *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1)))

/-- The named post-first-`sqrt zeta` mixed raw scalar in the fourth-term chain. -/
private noncomputable def switcherooAggregateMixedRawLocal
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) : Error :=
  avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
    ∑ g : Polynomial params, ∑ o : Outcome,
      ev ψbi
        ((leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (family.meas q.1).outcome g *
            (M q.2).outcome o)) *
          rightTensor (ι₁ := ι) ((family.meas q.1).outcome g)))

/-- Local wrapper for the first `sqrt chi` step in the fourth-term chain. -/
private lemma switcherooAggregateFourthTerm_close_once_commuted_raw_local
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
    |switcherooAggregateFourthTerm params ψbi family M -
        switcherooAggregateOnceCommutedRawLocal params ψbi family M| ≤
      Real.sqrt chi := by
  simpa [switcherooAggregateOnceCommutedRawLocal] using
    switcherooAggregateFourthTerm_split_close_once_commuted
      params ψbi hnorm family M chi hcomm

/-- Local wrapper for the second `sqrt zeta` raw fourth-term step. -/
private lemma switcherooAggregateFourthTerm_mixed_close_left_front_raw_local
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    |avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
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
                  (M q.2).outcome o)))| ≤
      Real.sqrt zeta := by
  let 𝒟q : Distribution (SlicePairQuestion params) :=
    uniformDistribution (SlicePairQuestion params)
  let A : SlicePairQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q g => leftTensor (ι₂ := ι) ((family.meas q.1).outcome g)
  let B : SlicePairQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q g => rightTensor (ι₁ := ι) ((family.meas q.1).outcome g)
  let C : SlicePairQuestion params → Polynomial params → Outcome → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q g o =>
      leftTensor (ι₂ := ι)
        ((completePartSubMeas params family q.1).total *
          (M q.2).outcome o *
          (family.meas q.1).outcome g *
          (M q.2).outcome o)
  have h𝒟q : ∑ q ∈ 𝒟q.support, 𝒟q.weight q ≤ 1 := by
    simpa [𝒟q] using uniformDistribution_weight_sum_le_one (SlicePairQuestion params)
  have hAherm : ∀ q g, (A q g)ᴴ = A q g := by
    intro q g
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((family.meas q.1).outcome_pos g))).isHermitian.eq
  have hBherm : ∀ q g, (B q g)ᴴ = B q g := by
    intro q g
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (rightTensor_nonneg (ι₁ := ι) ((family.meas q.1).outcome_pos g))).isHermitian.eq
  have hAB :
      avgOver 𝒟q
        (fun q => qSDDCore ψbi (fun g => (A q g)ᴴ) (fun g => (B q g)ᴴ)) ≤ zeta := by
    calc
      avgOver 𝒟q
          (fun q => qSDDCore ψbi (fun g => (A q g)ᴴ) (fun g => (B q g)ᴴ)) =
        avgOver 𝒟q
            (fun q => qSDDCore ψbi (A q) (B q)) := by
              apply avgOver_congr
              intro q
              unfold qSDDCore
              simp [hAherm q, hBherm q]
      _ ≤ zeta := by
            simpa [𝒟q, A, B] using
              switcherooCompletePartSelfConsistency_pairBound params ψbi family zeta hselfG
  have hC :
      ∀ q,
        (∑ g : Polynomial params,
            (∑ o : Outcome, C q g o)ᴴ * (∑ o : Outcome, C q g o)) ≤ 1 := by
    intro q
    simpa [C] using
      switcherooAggregateFourthTerm_once_commuted_contraction_right params family M q
  simpa [𝒟q, A, B, C] using
    (Preliminaries.closenessOfInnerProduct_right ψbi hnorm 𝒟q h𝒟q A B C zeta hAB hC)

private lemma switcherooAggregateLeftFrontRawLocal_point
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

private lemma switcherooAggregateFirstSplitRawLocal_point
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

private lemma switcherooAggregateMixedRawLocal_point
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

private lemma switcherooAggregateMixedRawLocal_close_leftFrontRawLocal
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    |switcherooAggregateMixedRawLocal params ψbi family M -
        switcherooAggregateLeftFrontRawLocal params ψbi family M| ≤ Real.sqrt zeta := by
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
        switcherooAggregateLeftFrontRawLocal params ψbi family M := by
    unfold switcherooAggregateLeftFrontRawLocal
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
        switcherooAggregateMixedRawLocal params ψbi family M := by
    unfold switcherooAggregateMixedRawLocal
    apply avgOver_congr
    intro q
    simpa [switcherooAggregateMixedRawLocal] using
      switcherooAggregateMixedRawLocal_point params ψbi family M q
  calc
    |switcherooAggregateMixedRawLocal params ψbi family M -
        switcherooAggregateLeftFrontRawLocal params ψbi family M|
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
      switcherooAggregateFourthTerm_mixed_close_left_front_raw_local
          params ψbi hnorm family M zeta hselfG

private lemma switcherooAggregateOnceCommutedRawLocal_point
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

private lemma switcherooAggregateOnceCommutedRawLocal_close_mixedLocal
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (zeta : Error)
    (hselfG : GCompleteSelfConsistencyStatement params ψbi family zeta) :
    |switcherooAggregateOnceCommutedRawLocal params ψbi family M -
        switcherooAggregateMixedRawLocal params ψbi family M| ≤ Real.sqrt zeta := by
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
        switcherooAggregateOnceCommutedRawLocal params ψbi family M := by
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
    exact switcherooAggregateOnceCommutedRawLocal_point params ψbi family M q
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
        switcherooAggregateMixedRawLocal params ψbi family M := by
    rfl
  calc
    |switcherooAggregateOnceCommutedRawLocal params ψbi family M -
        switcherooAggregateMixedRawLocal params ψbi family M|
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
        switcherooAggregateFourthTerm_once_commuted_close_mixed_local
          params ψbi hnorm family M zeta hselfG

private lemma switcherooAggregateFirstTerm_eq_leftSandwich_local
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooAggregateFirstTerm params ψbi family M =
      avgOver (uniformDistribution (SliceQuestion params))
        (fun x =>
          MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi
            (uniformDistribution (SliceQuestion params))
            M
            ((completePartSubMeas params family x).total)) := by
  unfold switcherooAggregateFirstTerm
  calc
    avgOver (uniformDistribution (SlicePairQuestion params))
        (fun q =>
          ∑ o : Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((M q.2).outcome o * (completePartSubMeas params family q.1).total *
                  (M q.2).outcome o)))
      = avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            avgOver (uniformDistribution (SliceQuestion params))
              (fun y =>
                ∑ o : Outcome,
                  ev ψbi
                    (leftTensor (ι₂ := ι)
                      ((M y).outcome o * (completePartSubMeas params family x).total *
                        (M y).outcome o)))) := by
            simpa [SlicePairQuestion, SliceQuestion] using
              (avgOver_uniform_prod
                (α := SliceQuestion params)
                (β := SliceQuestion params)
                (f := fun x y =>
                  ∑ o : Outcome,
                    ev ψbi
                      (leftTensor (ι₂ := ι)
                        ((M y).outcome o * (completePartSubMeas params family x).total *
                          (M y).outcome o))))
    _ = avgOver (uniformDistribution (SliceQuestion params))
          (fun x =>
            MIPStarRE.LDT.Preliminaries.leftSandwichExpectation ψbi
              (uniformDistribution (SliceQuestion params))
              M
              ((completePartSubMeas params family x).total)) := by
            apply avgOver_congr
            intro x
            simp [MIPStarRE.LDT.Preliminaries.leftSandwichExpectation,
              avgOver, leftTensor_mul_leftTensor, mul_assoc]

-- The last `χ`-step needs only pointwise normalization for the raw `G_g M_o`
-- factors inside `closenessOfInnerProduct_right`; the heavy adjoint rewrites are
-- isolated in the two pointwise helper lemmas above.
/-- The final `sqrt chi` bridge in the fourth-term chain: compare the left-front
raw scalar with the split-by-`g` scalar that later collapses to the first
positive switcheroo term. -/
private lemma switcherooAggregateLeftFrontRaw_close_firstSplitRaw
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
    |switcherooAggregateLeftFrontRawLocal params ψbi family M -
        switcherooAggregateFirstSplitRawLocal params ψbi family M| ≤
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
        switcherooAggregateFirstSplitRawLocal params ψbi family M := by
    unfold switcherooAggregateFirstSplitRawLocal
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
        switcherooAggregateLeftFrontRawLocal params ψbi family M := by
    unfold switcherooAggregateLeftFrontRawLocal
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
        switcherooAggregateFirstSplitRawLocal params ψbi family M := by
    simpa using hleft
  have hright' :
      avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome, ev ψbi (B q a * C q a ())) =
        switcherooAggregateLeftFrontRawLocal params ψbi family M := by
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

/-- SWAP symmetry identifies the two scalar centers used in the switcheroo
argument. -/
private lemma switcherooCompletePartCenter_eq_target
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hfix : swapDensity ψbi.density = ψbi.density)
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    avgOver (uniformDistribution (SliceQuestion params)) (fun y =>
      Preliminaries.middleSandwichExpectation ψbi
        (uniformDistribution (SliceQuestion params))
        (completePartProjFamily params family) (((M y).toSubMeas).total)) =
      switcherooAggregateTarget params ψbi family M := by
  calc
    avgOver (uniformDistribution (SliceQuestion params)) (fun y =>
        Preliminaries.middleSandwichExpectation ψbi
          (uniformDistribution (SliceQuestion params))
          (completePartProjFamily params family) (((M y).toSubMeas).total))
      = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ev ψbi
            (opTensor
              (((M q.2).toSubMeas).total)
              ((completePartSubMeas params family q.1).total))) := by
          simpa using
            switcherooAggregateMGCenterComplete_eq_opTensor_avg
              (ι := ι) (params := params) (ψbi := ψbi) (family := family) (M := M)
    _ = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ev ψbi
            (opTensor
              ((completePartSubMeas params family q.1).total)
              (((M q.2).toSubMeas).total))) := by
          apply avgOver_congr
          intro q
          simpa using
            (switcheroo_ev_opTensor_swap ψbi hfix
              (((M q.2).toSubMeas).total)
              ((completePartSubMeas params family q.1).total))
    _ = switcherooAggregateTarget params ψbi family M := by
          simpa using
            (switcherooAggregateTarget_eq_opTensor_avg
              (ι := ι) (params := params) (ψbi := ψbi) (family := family) (M := M)).symm

-- After extracting the pointwise normalization helpers above, the final
-- four-term packaging proof elaborates within the default heartbeat budget.
/-- `lem:commutativity-switcheroo`. -/
lemma commutativitySwitcheroo {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (hnorm : ψbi.IsNormalized)
    (hfix : swapDensity ψbi.density = ψbi.density)
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
  have hcenter : centerMGComplete = centerGM := by
    simpa [centerGM, centerMGComplete] using
      switcherooCompletePartCenter_eq_target params ψbi hfix family M
  have hsecond' : |secondTerm - centerGM| ≤ 2 * Real.sqrt zeta := by
    simpa [hcenter] using hsecond
  have hfirst_eq :
      switcherooAggregateFirstTerm params ψbi family M = firstTerm := by
    simpa [firstTerm, completePartSubMeas, postprocess_total] using
      switcherooAggregateFirstTerm_eq_leftSandwich_local params ψbi family M
  have hstep1 :=
    switcherooAggregateFourthTerm_close_once_commuted_raw_local
      params ψbi hnorm family M chi hcomm
  have hstep2 :
      |switcherooAggregateOnceCommutedRawLocal params ψbi family M -
          switcherooAggregateMixedRawLocal params ψbi family M| ≤ Real.sqrt zeta := by
    exact switcherooAggregateOnceCommutedRawLocal_close_mixedLocal
      params ψbi hnorm family M zeta hselfG
  have hstep3 :
      |switcherooAggregateMixedRawLocal params ψbi family M -
          switcherooAggregateLeftFrontRawLocal params ψbi family M| ≤ Real.sqrt zeta := by
    exact switcherooAggregateMixedRawLocal_close_leftFrontRawLocal
      params ψbi hnorm family M zeta hselfG
  have hstep4 :=
    switcherooAggregateLeftFrontRaw_close_firstSplitRaw
      params ψbi hnorm family M chi hcomm
  have hstep5 :
      switcherooAggregateFirstSplitRawLocal params ψbi family M =
        switcherooAggregateFirstTerm params ψbi family M := by
    simpa [switcherooAggregateFirstSplitRawLocal, mul_assoc] using
      switcherooAggregateFirstTerm_eq_split_by_g_local params ψbi family M
  have hstep5' :
      |switcherooAggregateFirstSplitRawLocal params ψbi family M -
          switcherooAggregateFirstTerm params ψbi family M| ≤ 0 := by
    rw [hstep5]
    simp
  have hfourth_first :
      |switcherooAggregateFourthTerm params ψbi family M -
          switcherooAggregateFirstTerm params ψbi family M| ≤
        2 * Real.sqrt zeta + 2 * Real.sqrt chi := by
    calc
      |switcherooAggregateFourthTerm params ψbi family M -
          switcherooAggregateFirstTerm params ψbi family M|
        ≤ |switcherooAggregateFourthTerm params ψbi family M -
              switcherooAggregateOnceCommutedRawLocal params ψbi family M| +
            |switcherooAggregateOnceCommutedRawLocal params ψbi family M -
              switcherooAggregateMixedRawLocal params ψbi family M| +
            |switcherooAggregateMixedRawLocal params ψbi family M -
              switcherooAggregateLeftFrontRawLocal params ψbi family M| +
            |switcherooAggregateLeftFrontRawLocal params ψbi family M -
              switcherooAggregateFirstSplitRawLocal params ψbi family M| +
            |switcherooAggregateFirstSplitRawLocal params ψbi family M -
              switcherooAggregateFirstTerm params ψbi family M| := by
              nlinarith [abs_sub_le
                (switcherooAggregateFourthTerm params ψbi family M)
                (switcherooAggregateOnceCommutedRawLocal params ψbi family M)
                (switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (switcherooAggregateOnceCommutedRawLocal params ψbi family M)
                  (switcherooAggregateMixedRawLocal params ψbi family M)
                  (switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (switcherooAggregateMixedRawLocal params ψbi family M)
                  (switcherooAggregateLeftFrontRawLocal params ψbi family M)
                  (switcherooAggregateFirstTerm params ψbi family M),
                abs_sub_le
                  (switcherooAggregateLeftFrontRawLocal params ψbi family M)
                  (switcherooAggregateFirstSplitRawLocal params ψbi family M)
                  (switcherooAggregateFirstTerm params ψbi family M)]
      _ ≤ Real.sqrt chi + Real.sqrt zeta + Real.sqrt zeta + Real.sqrt chi + 0 := by
            nlinarith [hstep1, hstep2, hstep3, hstep4, hstep5']
      _ = 2 * Real.sqrt zeta + 2 * Real.sqrt chi := by ring
  have hfourth_first' :
      |fourthTerm - firstTerm| ≤ 2 * Real.sqrt zeta + 2 * Real.sqrt chi := by
    rw [← hfirst_eq]
    simpa [fourthTerm] using hfourth_first
  have hfourth : |fourthTerm - centerGM| ≤
      2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by
    calc
      |fourthTerm - centerGM| ≤ |fourthTerm - firstTerm| + |firstTerm - centerGM| := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (abs_sub_le fourthTerm firstTerm centerGM)
      _ ≤ (2 * Real.sqrt zeta + 2 * Real.sqrt chi) + 2 * Real.sqrt omega := by
            exact add_le_add hfourth_first' hfirst
      _ = 2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by ring
  have hthird : |thirdTerm - centerGM| ≤
      2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega := by
    rw [hthird_eq]
    exact hfourth
  constructor
  unfold sddErrorOp
  rw [hexpand]
  have hdecomp :
      firstTerm + secondTerm - thirdTerm - fourthTerm ≤
        |firstTerm - centerGM| + |secondTerm - centerGM| +
          |thirdTerm - centerGM| + |fourthTerm - centerGM| := by
    have hfirst_le : firstTerm - centerGM ≤ |firstTerm - centerGM| := by
      exact le_abs_self _
    have hsecond_le : secondTerm - centerGM ≤ |secondTerm - centerGM| := by
      exact le_abs_self _
    have hthird_le : -(thirdTerm - centerGM) ≤ |thirdTerm - centerGM| := by
      exact neg_le_abs _
    have hfourth_le : -(fourthTerm - centerGM) ≤ |fourthTerm - centerGM| := by
      exact neg_le_abs _
    have hrewrite :
        firstTerm + secondTerm - thirdTerm - fourthTerm =
          (firstTerm - centerGM) + (secondTerm - centerGM) -
            (thirdTerm - centerGM) - (fourthTerm - centerGM) := by
      ring
    rw [hrewrite]
    nlinarith
  have hmain_eq :
      switcherooAggregateFirstTerm params ψbi family M + secondTerm - thirdTerm - fourthTerm =
        firstTerm + secondTerm - thirdTerm - fourthTerm := by
    exact congrArg (fun t => t + secondTerm - thirdTerm - fourthTerm) hfirst_eq
  calc
    switcherooAggregateFirstTerm params ψbi family M +
        switcherooAggregateSecondTerm params ψbi family M -
        switcherooAggregateThirdTerm params ψbi family M -
        switcherooAggregateFourthTerm params ψbi family M
      = firstTerm + secondTerm - thirdTerm - fourthTerm := by
          simpa [secondTerm, thirdTerm, fourthTerm] using hmain_eq
    _
      ≤ |firstTerm - centerGM| + |secondTerm - centerGM| +
          |thirdTerm - centerGM| + |fourthTerm - centerGM| := hdecomp
    _ ≤ 2 * Real.sqrt omega + 2 * Real.sqrt zeta +
          (2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega) +
          (2 * Real.sqrt zeta + 2 * Real.sqrt chi + 2 * Real.sqrt omega) := by
            nlinarith [hfirst, hsecond', hthird, hfourth]
    _ = commutativitySwitcherooError zeta omega chi := by
          simp [commutativitySwitcherooError, Real.sqrt_eq_rpow]
          ring

end MIPStarRE.LDT.Pasting
