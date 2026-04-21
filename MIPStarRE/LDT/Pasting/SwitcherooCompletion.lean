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

private lemma switcheroo_swapDensity_eq_reindex
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity X = Matrix.reindex (Equiv.prodComm ι ι) (Equiv.prodComm ι ι) X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

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
        ∑ u : Unit,
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
        ∑ u : Unit,
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

/- Heartbeat budget: this `χ`-transfer expands the raw split-by-`g` scalar,
normalizes adjoints of `G_g M_o`, and then runs one `closenessOfInnerProduct_right`
step over the full `Polynomial × Outcome` family. The proof is stable but still
requires substantially more elaboration than the default budget. -/
set_option maxHeartbeats 50000000 in
-- The last `χ`-step needs explicit adjoint normalization for the raw `G_g M_o`
-- factors inside `closenessOfInnerProduct_right`.
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
    fun q go => (switcherooPointProductRight params family M q).outcome go
  let B : SlicePairQuestion params → Polynomial params × Outcome → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go => (switcherooPointProductLeft params family M q).outcome go
  let C : SlicePairQuestion params → Polynomial params × Outcome → Unit →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go _ => leftTensor (ι₂ := ι)
      (((family.meas q.1).outcome go.1) * (M q.2).outcome go.2)
  have h𝒟q : ∑ q ∈ 𝒟q.support, 𝒟q.weight q ≤ 1 := by
    simpa [𝒟q] using uniformDistribution_weight_sum_le_one (SlicePairQuestion params)
  have hAfun : ∀ q,
      (fun go => (A q go)ᴴ) =
        fun go => (switcherooPointProductLeft params family M q).outcome go := by
    intro q
    funext go
    rcases go with ⟨g, o⟩
    change (leftTensor (ι₂ := ι)
        (((M q.2).outcome o * (family.meas q.1).outcome g)))ᴴ =
      leftTensor (ι₂ := ι)
        ((family.meas q.1).outcome g * (M q.2).outcome o)
    rw [show
      (leftTensor (ι₂ := ι)
          (((M q.2).outcome o * (family.meas q.1).outcome g)))ᴴ =
        leftTensor (ι₂ := ι)
          ((((M q.2).outcome o * (family.meas q.1).outcome g))ᴴ) by
        simpa [leftTensor, opTensor] using
          (conjTranspose_opTensor
            (((M q.2).outcome o * (family.meas q.1).outcome g))
            (1 : MIPStarRE.Quantum.Op ι))]
    simp [Matrix.conjTranspose_mul,
      (family.meas q.1).outcome_hermitian g, (M q.2).outcome_hermitian o]
  have hBfun : ∀ q,
      (fun go => (B q go)ᴴ) =
        fun go => (switcherooPointProductRight params family M q).outcome go := by
    intro q
    funext go
    rcases go with ⟨g, o⟩
    change (leftTensor (ι₂ := ι)
        (((family.meas q.1).outcome g * (M q.2).outcome o)))ᴴ =
      leftTensor (ι₂ := ι)
        ((M q.2).outcome o * (family.meas q.1).outcome g)
    rw [show
      (leftTensor (ι₂ := ι)
          (((family.meas q.1).outcome g * (M q.2).outcome o)))ᴴ =
        leftTensor (ι₂ := ι)
          ((((family.meas q.1).outcome g * (M q.2).outcome o))ᴴ) by
        simpa [leftTensor, opTensor] using
          (conjTranspose_opTensor
            (((family.meas q.1).outcome g * (M q.2).outcome o))
            (1 : MIPStarRE.Quantum.Op ι))]
    simp [Matrix.conjTranspose_mul,
      (family.meas q.1).outcome_hermitian g, (M q.2).outcome_hermitian o]
  have hAB :
      avgOver 𝒟q
        (fun q => qSDDCore ψbi (fun go => (A q go)ᴴ) (fun go => (B q go)ᴴ)) ≤ chi := by
    calc
      avgOver 𝒟q
          (fun q => qSDDCore ψbi (fun go => (A q go)ᴴ) (fun go => (B q go)ᴴ)) =
        avgOver 𝒟q
          (fun q => qSDDCore ψbi
            (fun go => (switcherooPointProductLeft params family M q).outcome go)
            (fun go => (switcherooPointProductRight params family M q).outcome go)) := by
              apply avgOver_congr
              intro q
              rw [hAfun q, hBfun q]
      _ ≤ chi := by
            simpa [𝒟q] using
              switcherooPointProductCommutation_coreBound params ψbi family M chi hcomm
  have hC :
      ∀ q,
        (∑ go : Polynomial params × Outcome,
            (∑ u : Unit, C q go u)ᴴ * (∑ u : Unit, C q go u)) ≤ 1 := by
    intro q
    simpa [C] using switcherooAggregateLeftFront_contraction params family M q
  have hleft :
      avgOver 𝒟q (fun q =>
          ∑ go : Polynomial params × Outcome,
            ∑ u : Unit, ev ψbi (B q go * C q go u)) =
        switcherooAggregateLeftFrontRawLocal params ψbi family M := by
    apply avgOver_congr
    intro q
    simpa [B, C, switcherooAggregateLeftFrontRawLocal] using
      switcherooAggregateLeftFrontRawLocal_point params ψbi family M q
  have hright :
      avgOver 𝒟q (fun q =>
          ∑ go : Polynomial params × Outcome,
            ∑ u : Unit, ev ψbi (A q go * C q go u)) =
        switcherooAggregateFirstSplitRawLocal params ψbi family M := by
    apply avgOver_congr
    intro q
    simpa [A, C, switcherooAggregateFirstSplitRawLocal, mul_assoc] using
      switcherooAggregateFirstSplitRawLocal_point params ψbi family M q
  have hclose :=
    Preliminaries.closenessOfInnerProduct_right ψbi hnorm 𝒟q h𝒟q A B C chi hAB hC
  calc
    |switcherooAggregateLeftFrontRawLocal params ψbi family M -
        switcherooAggregateFirstSplitRawLocal params ψbi family M|
      = |avgOver 𝒟q (fun q =>
            ∑ go : Polynomial params × Outcome,
              ∑ u : Unit, ev ψbi (B q go * C q go u)) -
          avgOver 𝒟q (fun q =>
            ∑ go : Polynomial params × Outcome,
              ∑ u : Unit, ev ψbi (A q go * C q go u))| := by
            rw [hleft, hright, abs_sub_comm]
    _ ≤ Real.sqrt chi := by
          simpa [abs_sub_comm] using hclose

/- Heartbeat budget: the center-identification proof expands two nested uniform
averages and rewrites them through SWAP symmetry before collapsing back to the
target scalar center. This normalization-heavy `avgOver` / `rightTensor` rewrite
is stable at 10M heartbeats. -/
set_option maxHeartbeats 10000000 in
-- Expanding the nested averages and total operators for the center comparison is
-- expensive enough to require a larger heartbeat budget.
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
      = avgOver (uniformDistribution (SliceQuestion params)) (fun y =>
          avgOver (uniformDistribution (SliceQuestion params)) (fun x =>
            ev ψbi
              (leftTensor (ι₂ := ι) (((M y).toSubMeas).total) *
                rightTensor (ι₁ := ι) ((completePartSubMeas params family x).total)))) := by
            apply avgOver_congr
            intro y
            simp [Preliminaries.middleSandwichExpectation, completePartProjFamily]
    _ = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ev ψbi
            (leftTensor (ι₂ := ι) (((M q.2).toSubMeas).total) *
              rightTensor (ι₁ := ι) ((completePartSubMeas params family q.1).total))) := by
            let F : SliceQuestion params → SliceQuestion params → Error :=
              fun y x =>
                ev ψbi
                  (leftTensor (ι₂ := ι) (((M y).toSubMeas).total) *
                    rightTensor (ι₁ := ι) ((completePartSubMeas params family x).total))
            have hprod :
                avgOver (uniformDistribution (SliceQuestion params)) (fun y =>
                    avgOver (uniformDistribution (SliceQuestion params)) (fun x => F y x)) =
                  avgOver (uniformDistribution (SlicePairQuestion params))
                    (fun q => F q.1 q.2) := by
              simpa [SlicePairQuestion, SliceQuestion] using
                (avgOver_uniform_prod
                  (α := SliceQuestion params)
                  (β := SliceQuestion params)
                  (f := F)).symm
            have hswap :
                avgOver (uniformDistribution (SlicePairQuestion params))
                    (fun q => F q.1 q.2) =
                  avgOver (uniformDistribution (SlicePairQuestion params))
                    (fun q => F q.2 q.1) := by
              simpa [SlicePairQuestion, F] using
                (avgOver_uniform_equiv
                  (e := Equiv.prodComm (SliceQuestion params) (SliceQuestion params))
                  (f := fun q : SlicePairQuestion params => F q.1 q.2))
            calc
              avgOver (uniformDistribution (SliceQuestion params)) (fun y =>
                  avgOver (uniformDistribution (SliceQuestion params)) (fun x => F y x))
                = avgOver (uniformDistribution (SlicePairQuestion params))
                    (fun q => F q.1 q.2) := hprod
              _ = avgOver (uniformDistribution (SlicePairQuestion params))
                    (fun q => F q.2 q.1) := hswap
              _ = avgOver (uniformDistribution (SlicePairQuestion params))
                    (fun q =>
                      ev ψbi
                        (leftTensor (ι₂ := ι) (((M q.2).toSubMeas).total) *
                          rightTensor (ι₁ := ι)
                            ((completePartSubMeas params family q.1).total))) := by
                          rfl
    _ = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ev ψbi
            (leftTensor (ι₂ := ι) ((completePartSubMeas params family q.1).total) *
              rightTensor (ι₁ := ι) (((M q.2).toSubMeas).total))) := by
            apply avgOver_congr
            intro q
            simpa [leftTensor_mul_rightTensor_eq_opTensor] using
              switcheroo_ev_opTensor_swap ψbi hfix (((M q.2).toSubMeas).total)
                ((completePartSubMeas params family q.1).total)
    _ = switcherooAggregateTarget params ψbi family M := by
          unfold switcherooAggregateTarget
          apply avgOver_congr
          intro q
          rw [show ((M q.2).toSubMeas).total = ∑ o : Outcome, (M q.2).outcome o by
            exact (M q.2).sum_eq_total.symm]
          calc
            ev ψbi
                (leftTensor (ι₂ := ι) ((completePartSubMeas params family q.1).total) *
                  rightTensor (ι₁ := ι) (∑ o : Outcome, (M q.2).outcome o))
              = ev ψbi
                  (leftTensor (ι₂ := ι) ((completePartSubMeas params family q.1).total) *
                    ∑ o : Outcome, rightTensor (ι₁ := ι) ((M q.2).outcome o)) := by
                      congr 1
                      rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ]
            _ = ev ψbi
                  (∑ o : Outcome,
                    leftTensor (ι₂ := ι) ((completePartSubMeas params family q.1).total) *
                      rightTensor (ι₁ := ι) ((M q.2).outcome o)) := by
                        rw [Matrix.mul_sum]
            _ = ∑ o : Outcome,
                  ev ψbi
                    (leftTensor (ι₂ := ι) ((completePartSubMeas params family q.1).total) *
                      rightTensor (ι₁ := ι) ((M q.2).outcome o)) := by
                        rw [ev_sum]

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

-- The four-term expansion + triangle chain contains several large `calc`
-- blocks and raw-expression rewrites.
/- Heartbeat budget: `commutativitySwitcheroo` packages the full four-term
triangle chain from `lem:commutativity-switcheroo`, including the raw `χ, ζ, ζ, χ`
transfers and the final absolute-value decomposition. The large budget is for
proof elaboration of those scalar rewrites, not for search. -/
set_option maxHeartbeats 50000000 in
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

private lemma completePartAggregateCommutation_as_total
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
private lemma firstSwitcherooError_le_commutingWithGCompleteError
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
