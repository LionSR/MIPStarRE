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

/-- Rewrite the mixed switcheroo scalar in the tensor order expected by the raw
left-front transfer lemma. -/
lemma switcherooMixed_eq_rightTensor_leftTensor
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
      ∑ g : Polynomial params, ∑ o : Outcome,
        ev ψbi
          ((leftTensor (ι₂ := ι)
            ((completePartSubMeas params family q.1).total *
              (M q.2).outcome o *
              (family.meas q.1).outcome g *
              (M q.2).outcome o)) *
            rightTensor (ι₁ := ι) ((family.meas q.1).outcome g))) =
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ g : Polynomial params, ∑ o : Outcome,
          ev ψbi
            (rightTensor (ι₁ := ι) ((family.meas q.1).outcome g) *
              leftTensor (ι₂ := ι)
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (family.meas q.1).outcome g *
                  (M q.2).outcome o))) := by
  apply avgOver_congr
  intro q
  refine Finset.sum_congr rfl ?_
  intro g _
  refine Finset.sum_congr rfl ?_
  intro o _
  rw [leftTensor_mul_rightTensor_eq_opTensor,
    ← rightTensor_mul_leftTensor_eq_opTensor]

/-- Rewrite the left-front scalar in the tensor-product form expected by the raw
left-front transfer lemma. -/
lemma switcherooLeftFrontCoreScalar_eq_leftTensor_mul_leftTensor
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι) :
    switcherooLeftFrontCoreScalar params ψbi family M =
      avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
        ∑ g : Polynomial params, ∑ o : Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι) ((family.meas q.1).outcome g) *
              leftTensor (ι₂ := ι)
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome o *
                  (family.meas q.1).outcome g *
                  (M q.2).outcome o))) := by
  unfold switcherooLeftFrontCoreScalar
  apply avgOver_congr
  intro q
  rw [show
      (∑ go : Polynomial params × Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι)
              (((family.meas q.1).outcome go.1) *
                (M q.2).outcome go.2 *
                (family.meas q.1).outcome go.1 *
                (M q.2).outcome go.2))) =
        ∑ g : Polynomial params, ∑ o : Outcome,
          ev ψbi
            (leftTensor (ι₂ := ι)
              ((family.meas q.1).outcome g *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o)) by
    simpa using
      (Fintype.sum_prod_type' (f := fun g o =>
        ev ψbi
          (leftTensor (ι₂ := ι)
            ((family.meas q.1).outcome g *
              (M q.2).outcome o *
              (family.meas q.1).outcome g *
              (M q.2).outcome o))))]
  refine Finset.sum_congr rfl ?_
  intro g _
  refine Finset.sum_congr rfl ?_
  intro o _
  have hGabsorb :
      (family.meas q.1).outcome g *
          (completePartSubMeas params family q.1).total =
        (family.meas q.1).outcome g := by
    rw [completePartSubMeas_total]
    exact Preliminaries.projSubMeas_outcome_mul_total_eq_outcome
      (family.meas q.1) g
  have hcollapse :
      (family.meas q.1).outcome g *
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (family.meas q.1).outcome g *
            (M q.2).outcome o) =
        (family.meas q.1).outcome g *
          (M q.2).outcome o *
          (family.meas q.1).outcome g *
          (M q.2).outcome o := by
    calc
      (family.meas q.1).outcome g *
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome o *
            (family.meas q.1).outcome g *
            (M q.2).outcome o)
        = ((family.meas q.1).outcome g *
              (completePartSubMeas params family q.1).total) *
            (M q.2).outcome o *
            (family.meas q.1).outcome g *
            (M q.2).outcome o := by
              simp [mul_assoc]
      _ = (family.meas q.1).outcome g *
            (M q.2).outcome o *
            (family.meas q.1).outcome g *
            (M q.2).outcome o := by rw [hGabsorb]
  rw [leftTensor_mul_leftTensor]
  exact congrArg (fun X => ev ψbi (leftTensor (ι₂ := ι) X)) hcollapse.symm

-- The explicit left-front contraction proof still expands several product-indexed sums,
-- but the expensive pointwise normalizations now live in reusable helper lemmas,
-- so it now elaborates within the default heartbeat budget.
/-- The final `sqrt chi` step in the fourth-term switcheroo chain. -/
lemma switcherooLeftFront_close_firstSplitCore
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
    |switcherooLeftFrontCoreScalar params ψbi family M -
        switcherooFirstSplitCoreScalar params ψbi family M| ≤
      Real.sqrt chi := by
  let 𝒟q : Distribution (SlicePairQuestion params) :=
    uniformDistribution (SlicePairQuestion params)
  let A : SlicePairQuestion params → Polynomial params × Outcome → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go => ((switcherooPointProductLeft params family M q).outcome go)ᴴ
  let B : SlicePairQuestion params → Polynomial params × Outcome → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go => ((switcherooPointProductRight params family M q).outcome go)ᴴ
  let C : SlicePairQuestion params →
      Polynomial params × Outcome → Unit → MIPStarRE.Quantum.Op (ι × ι) :=
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
    simpa [C] using switcherooAggregateLeftFront_contraction params family M q
  have hclose :=
    Preliminaries.closenessOfInnerProduct_right ψbi hnorm 𝒟q h𝒟q A B C chi hAB hC
  have hleft :
      avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome,
            ∑ b : Unit, ev ψbi (A q a * C q a b)) =
        switcherooFirstSplitCoreScalar params ψbi family M := by
    unfold switcherooFirstSplitCoreScalar
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
  have hright :
      avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome,
            ∑ b : Unit, ev ψbi (B q a * C q a b)) =
        switcherooLeftFrontCoreScalar params ψbi family M := by
    unfold switcherooLeftFrontCoreScalar
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
        switcherooFirstSplitCoreScalar params ψbi family M := by
    simpa using hleft
  have hright' :
      avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome, ev ψbi (B q a * C q a ())) =
        switcherooLeftFrontCoreScalar params ψbi family M := by
    simpa using hright
  have hclose' :
      |avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome, ev ψbi (A q a * C q a ())) -
        avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome, ev ψbi (B q a * C q a ()))| ≤
        Real.sqrt chi := by
    simpa using hclose
  simpa [hleft', hright', abs_sub_comm] using hclose'

set_option maxHeartbeats 3000000 in
-- Expanding `qSDDOp` into four averaged scalar terms over a slice-pair question
-- generates a large normalization expression that otherwise exceeds heartbeats.
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
