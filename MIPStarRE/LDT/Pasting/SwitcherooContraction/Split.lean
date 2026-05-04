import MIPStarRE.LDT.Pasting.SwitcherooSetup.Terms

/-!
# Section 12 pasting: switcheroo split contraction

The split-form contraction and first mixed-term transfer.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Shared switcheroo contraction helper package -/

/-- The `g`-indexed sandwich family used in the once-commuted contraction bounds. -/
noncomputable def switcherooAggregateFourthTermX
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    Polynomial params → MIPStarRE.Quantum.Op ι :=
  fun g => ∑ o : Outcome, (M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o

/-- The complete-part total operator is Hermitian. -/
lemma switcherooCompletePartTotal_hermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    ((completePartSubMeas params family q.1).total)ᴴ = (completePartSubMeas params family q.1).total :=
  (Matrix.nonneg_iff_posSemidef.mp
    (SubMeas.total_nonneg (completePartSubMeas params family q.1))).isHermitian.eq

/-- The complete-part total operator is idempotent. -/
lemma switcherooCompletePartTotal_sq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (completePartSubMeas params family q.1).total *
        (completePartSubMeas params family q.1).total =
      (completePartSubMeas params family q.1).total := by
  simpa [completePartSubMeas, postprocess_total] using
    projSubMeas_total_sq (family.meas q.1)

/-- The complete-part total operator is bounded by the identity. -/
lemma switcherooCompletePartTotal_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params) :
    (completePartSubMeas params family q.1).total ≤ 1 :=
  (completePartSubMeas params family q.1).total_le_one

/-- Every outcome of the external projective family is Hermitian. -/
lemma switcherooMeasuredOutcome_hermitian
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (o : Outcome) :
    ((M q.2).outcome o)ᴴ = (M q.2).outcome o :=
  (Matrix.nonneg_iff_posSemidef.mp ((M q.2).outcome_pos o)).isHermitian.eq

/-- Every slice outcome of the completed family is Hermitian. -/
lemma switcherooSliceOutcome_hermitian
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (q : SlicePairQuestion params)
    (g : Polynomial params) :
    ((family.meas q.1).outcome g)ᴴ = (family.meas q.1).outcome g :=
  (Matrix.nonneg_iff_posSemidef.mp ((family.meas q.1).outcome_pos g)).isHermitian.eq

/-- The shared `X_g` sandwich family is Hermitian pointwise. -/
lemma switcherooAggregateFourthTermX_hermitian
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (g : Polynomial params) :
    (switcherooAggregateFourthTermX params family M q g)ᴴ =
      switcherooAggregateFourthTermX params family M q g := by
  unfold switcherooAggregateFourthTermX
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl ?_
  intro o _
  simp [Matrix.conjTranspose_mul, switcherooMeasuredOutcome_hermitian params M q o,
    switcherooSliceOutcome_hermitian params family q g, mul_assoc]

/-- The shared `X_g` sandwich family is positive semidefinite pointwise. -/
lemma switcherooAggregateFourthTermX_nonneg
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (g : Polynomial params) :
    0 ≤ switcherooAggregateFourthTermX params family M q g := by
  unfold switcherooAggregateFourthTermX
  refine Finset.sum_nonneg ?_
  intro o _
  exact MIPStarRE.Quantum.sandwich_nonneg ((family.meas q.1).outcome_pos g)
    (switcherooMeasuredOutcome_hermitian params M q o)

/-- The shared `X_g` sandwich family is bounded by the identity pointwise. -/
lemma switcherooAggregateFourthTermX_le_one
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (g : Polynomial params) :
    switcherooAggregateFourthTermX params family M q g ≤ 1 :=
  projSubMeas_sandwich_sum_le_one (M q.2) ((family.meas q.1).outcome g)
    ((family.meas q.1).outcome_le_one g)

/-- The shared `X_g` sandwich family satisfies `X_g^2 ≤ X_g`. -/
lemma switcherooAggregateFourthTermX_sq_le
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params)
    (g : Polynomial params) :
    switcherooAggregateFourthTermX params family M q g *
        switcherooAggregateFourthTermX params family M q g ≤
      switcherooAggregateFourthTermX params family M q g :=
  MIPStarRE.Quantum.sq_le_self
    (switcherooAggregateFourthTermX_nonneg params family M q g)
    (switcherooAggregateFourthTermX_le_one params family M q g)

/-- Summing the shared `X_g` family collapses to the middle sandwich term. -/
lemma switcherooAggregateFourthTermX_sum
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    ∑ g : Polynomial params, switcherooAggregateFourthTermX params family M q g =
      ∑ o : Outcome,
        (M q.2).outcome o * (completePartSubMeas params family q.1).total * (M q.2).outcome o := by
  unfold switcherooAggregateFourthTermX
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro o _
  calc
    ∑ g : Polynomial params, (M q.2).outcome o * (family.meas q.1).outcome g * (M q.2).outcome o
      = (M q.2).outcome o * (∑ g : Polynomial params, (family.meas q.1).outcome g) * (M q.2).outcome o := by
          simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
    _ = (M q.2).outcome o * (completePartSubMeas params family q.1).total * (M q.2).outcome o := by
          rw [(family.meas q.1).sum_eq_total]
          simp [completePartSubMeas, postprocess_total]

/-- The middle sandwich sum used in the contraction bounds is a contraction. -/
lemma switcherooAggregateFourthTerm_middle_sum_le_one
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    ∑ o : Outcome,
        (M q.2).outcome o * (completePartSubMeas params family q.1).total * (M q.2).outcome o ≤ 1 :=
  projSubMeas_sandwich_sum_le_one (M q.2) ((completePartSubMeas params family q.1).total)
    (switcherooCompletePartTotal_le_one params family q)

/-- Contraction witness for the first `sqrt chi` switcheroo transfer. -/
private lemma switcherooAggregateFourthTerm_split_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (M : IdxProjSubMeas (Fq params) Outcome ι)
    (q : SlicePairQuestion params) :
    (∑ go : Polynomial params × Outcome,
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1)) *
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1))ᴴ) ≤ 1 := by
  let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family q.1).total
  let Gq : Polynomial params → MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome
  let Mo : Outcome → MIPStarRE.Quantum.Op ι := (M q.2).outcome
  have hGherm : Gᴴ = G := by
    simpa [G] using switcherooCompletePartTotal_hermitian params family q
  have hGsq : G * G = G := by
    simpa [G] using switcherooCompletePartTotal_sq params family q
  have hMoherm : ∀ o : Outcome, (Mo o)ᴴ = Mo o := by
    intro o
    simpa [Mo] using switcherooMeasuredOutcome_hermitian params M q o
  have hGqherm : ∀ g : Polynomial params, (Gq g)ᴴ = Gq g := by
    intro g
    simpa [Gq] using switcherooSliceOutcome_hermitian params family q g
  have hsum :
      (∑ go : Polynomial params × Outcome,
          (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1)) *
            (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1))ᴴ) =
        leftTensor (ι₂ := ι) (G * (∑ o : Outcome, Mo o * G * Mo o) * G) := by
    calc
      (∑ go : Polynomial params × Outcome,
          (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1)) *
            (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1))ᴴ)
        = ∑ go : Polynomial params × Outcome,
            leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1 * Mo go.2 * G) := by
              refine Finset.sum_congr rfl ?_
              intro go _
              calc
                (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1)) *
                    (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1))ᴴ
                  = (leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1)) *
                      leftTensor (ι₂ := ι) ((G * Mo go.2 * Gq go.1)ᴴ) := by
                        congr 2
                        simpa [leftTensor, opTensor] using
                          (conjTranspose_opTensor (G * Mo go.2 * Gq go.1)
                            (1 : MIPStarRE.Quantum.Op ι))
                _ = leftTensor (ι₂ := ι)
                      ((G * Mo go.2 * Gq go.1) * (G * Mo go.2 * Gq go.1)ᴴ) := by
                        rw [leftTensor_mul_leftTensor]
                _ = leftTensor (ι₂ := ι) (G * Mo go.2 * Gq go.1 * Mo go.2 * G) := by
                        congr 1
                        calc
                          (G * Mo go.2 * Gq go.1) * (G * Mo go.2 * Gq go.1)ᴴ
                            = G * (Mo go.2 * (Gq go.1 * (Gq go.1 * (Mo go.2 * G)))) := by
                                simp [Matrix.conjTranspose_mul, mul_assoc, hGherm,
                                  hMoherm, hGqherm]
                          _ = G * (Mo go.2 * (Gq go.1 * (Mo go.2 * G))) := by
                                have hproj : Gq go.1 * Gq go.1 = Gq go.1 := by
                                  simpa [Gq] using (family.meas q.1).proj go.1
                                congr 1
                                congr 1
                                rw [← mul_assoc, hproj]
                          _ = G * Mo go.2 * Gq go.1 * Mo go.2 * G := by
                                simp [mul_assoc]
      _ = ∑ g : Polynomial params,
            ∑ o : Outcome, leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o * G) := by
            simpa using
              (Fintype.sum_prod_type' (f := fun g o =>
                leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o * G)))
      _ = ∑ g : Polynomial params,
            leftTensor (ι₂ := ι) (∑ o : Outcome, G * Mo o * Gq g * Mo o * G) := by
            refine Finset.sum_congr rfl ?_
            intro g _
            rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
      _ = leftTensor (ι₂ := ι)
            (∑ g : Polynomial params, ∑ o : Outcome, G * Mo o * Gq g * Mo o * G) := by
            rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ]
      _ = leftTensor (ι₂ := ι) (∑ o : Outcome, G * Mo o * G * Mo o * G) := by
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro o _
            calc
              ∑ g : Polynomial params, G * Mo o * Gq g * Mo o * G
                = G * Mo o * (∑ g : Polynomial params, Gq g) * Mo o * G := by
                    simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
              _ = G * Mo o * G * Mo o * G := by
                    rw [(family.meas q.1).sum_eq_total]
                    simp [G]
      _ = leftTensor (ι₂ := ι) (G * (∑ o : Outcome, Mo o * G * Mo o) * G) := by
            congr 1
            simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
  have hmid_le : ∑ o : Outcome, Mo o * G * Mo o ≤ 1 := by
    simpa [G, Mo] using switcherooAggregateFourthTerm_middle_sum_le_one params family M q
  have hsandwich_le : G * (∑ o : Outcome, Mo o * G * Mo o) * G ≤ G := by
    calc
      G * (∑ o : Outcome, Mo o * G * Mo o) * G ≤ G * 1 * G := by
        exact MIPStarRE.Quantum.sandwich_mono hGherm hmid_le
      _ = G := by simp [hGsq]
  calc
    (∑ go : Polynomial params × Outcome,
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1)) *
        (leftTensor (ι₂ := ι)
          ((completePartSubMeas params family q.1).total *
            (M q.2).outcome go.2 *
            (family.meas q.1).outcome go.1))ᴴ)
      = leftTensor (ι₂ := ι) (G * (∑ o : Outcome, Mo o * G * Mo o) * G) := by
          simpa [G, Gq, Mo] using hsum
    _ ≤ leftTensor (ι₂ := ι) G := by
          simpa [leftTensor, opTensor] using
            (opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
              hsandwich_le (show (0 : MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one))
    _ ≤ 1 := by
          simpa [G] using leftTensor_le_one (ι₂ := ι)
            ((completePartSubMeas params family q.1).total_le_one)

/-- The first `sqrt chi` step in the fourth-term switcheroo chain. -/
lemma switcherooAggregateFourthTerm_split_close_once_commuted
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
        avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ go : Polynomial params × Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1 *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1)))| ≤
      Real.sqrt chi := by
  let 𝒟q : Distribution (SlicePairQuestion params) :=
    uniformDistribution (SlicePairQuestion params)
  let A : SlicePairQuestion params → Polynomial params × Outcome → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go => (switcherooPointProductLeft params family M q).outcome go
  let B : SlicePairQuestion params → Polynomial params × Outcome → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go => (switcherooPointProductRight params family M q).outcome go
  let C : SlicePairQuestion params →
      Polynomial params × Outcome → Unit → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q go () =>
      leftTensor (ι₂ := ι)
        ((completePartSubMeas params family q.1).total *
          (M q.2).outcome go.2 *
          (family.meas q.1).outcome go.1)
  have h𝒟q : ∑ q ∈ 𝒟q.support, 𝒟q.weight q ≤ 1 := by
    simpa [𝒟q] using uniformDistribution_weight_sum_le_one (SlicePairQuestion params)
  have hAB : avgOver 𝒟q (fun q => qSDDCore ψbi (A q) (B q)) ≤ chi := by
    simpa [𝒟q, A, B] using
      switcherooPointProductCommutation_coreBound params ψbi family M chi hcomm
  have hC :
      ∀ q,
        (∑ go : Polynomial params × Outcome,
            (∑ u : Unit, C q go u) * (∑ u : Unit, C q go u)ᴴ) ≤ 1 := by
    intro q
    simpa [C] using switcherooAggregateFourthTerm_split_contraction params family M q
  have hclose :=
    Preliminaries.closenessOfInnerProduct_left ψbi hnorm 𝒟q h𝒟q A B C chi hAB hC
  have hleft :
      avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome,
            ev ψbi (C q a () * A q a)) =
        switcherooAggregateFourthTerm params ψbi family M := by
    calc
      avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome,
            ev ψbi (C q a () * A q a))
        = avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
            ∑ go : Polynomial params × Outcome,
              ev ψbi
                (leftTensor (ι₂ := ι)
                  ((completePartSubMeas params family q.1).total *
                    (M q.2).outcome go.2 *
                    (family.meas q.1).outcome go.1 *
                    (family.meas q.1).outcome go.1 *
                    (M q.2).outcome go.2))) := by
              simp [𝒟q, A, C, switcherooPointProductLeft, orderedProductOpFamily,
                OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc]
      _ = switcherooAggregateFourthTerm params ψbi family M := by
            symm
            exact switcherooAggregateFourthTerm_eq_split params ψbi family M
  have hright :
      avgOver 𝒟q (fun q =>
          ∑ a : Polynomial params × Outcome,
            ev ψbi (C q a () * B q a)) =
        avgOver (uniformDistribution (SlicePairQuestion params)) (fun q =>
          ∑ go : Polynomial params × Outcome,
            ev ψbi
              (leftTensor (ι₂ := ι)
                ((completePartSubMeas params family q.1).total *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1 *
                  (M q.2).outcome go.2 *
                  (family.meas q.1).outcome go.1))) := by
    simp [𝒟q, B, C, switcherooPointProductRight, reversedProductOpFamily,
      OpFamily.leftPlacedOpFamily, leftTensor_mul_leftTensor, mul_assoc]
  simpa [hleft, hright] using hclose

/-- Left-action contraction witness for the first `sqrt zeta` transfer. -/
private lemma switcherooAggregateFourthTerm_once_commuted_contraction_left
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
                (M q.2).outcome o)) *
          (∑ o : Outcome,
            leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))ᴴ) ≤ 1 := by
  let G : MIPStarRE.Quantum.Op ι := (completePartSubMeas params family q.1).total
  let Gq : Polynomial params → MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome
  let Mo : Outcome → MIPStarRE.Quantum.Op ι := (M q.2).outcome
  let X : Polynomial params → MIPStarRE.Quantum.Op ι :=
    switcherooAggregateFourthTermX params family M q
  have hGherm : Gᴴ = G := by
    simpa [G] using switcherooCompletePartTotal_hermitian params family q
  have hGsq : G * G = G := by
    simpa [G] using switcherooCompletePartTotal_sq params family q
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
  have hsum :
      (∑ g : Polynomial params,
          (∑ o : Outcome, leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o)) *
            (∑ o : Outcome, leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o))ᴴ) =
        ∑ g : Polynomial params, leftTensor (ι₂ := ι) (G * X g * X g * G) := by
    refine Finset.sum_congr rfl ?_
    intro g _
    calc
      (∑ o : Outcome, leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o)) *
          (∑ o : Outcome, leftTensor (ι₂ := ι) (G * Mo o * Gq g * Mo o))ᴴ
        = leftTensor (ι₂ := ι) (G * X g) * (leftTensor (ι₂ := ι) (G * X g))ᴴ := by
            congr 2
            · rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
                (fun o : Outcome => G * Mo o * Gq g * Mo o)]
              congr 1
              simpa [X, switcherooAggregateFourthTermX, mul_assoc] using
                (Finset.mul_sum (s := Finset.univ) (a := G)
                  (f := fun o : Outcome => Mo o * Gq g * Mo o)).symm
            · rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
                (fun o : Outcome => G * Mo o * Gq g * Mo o)]
              congr 1
              simpa [X, switcherooAggregateFourthTermX, mul_assoc] using
                (Finset.mul_sum (s := Finset.univ) (a := G)
                  (f := fun o : Outcome => Mo o * Gq g * Mo o)).symm
      _ = leftTensor (ι₂ := ι) (G * X g) * leftTensor (ι₂ := ι) ((G * X g)ᴴ) := by
            congr 2
            simpa [leftTensor, opTensor] using
              (conjTranspose_opTensor (G * X g) (1 : MIPStarRE.Quantum.Op ι))
      _ = leftTensor (ι₂ := ι) ((G * X g) * (G * X g)ᴴ) := by
            rw [leftTensor_mul_leftTensor]
      _ = leftTensor (ι₂ := ι) (G * X g * X g * G) := by
            simp [Matrix.conjTranspose_mul, hGherm, hXherm g, mul_assoc]
  have hsandwichSum_le :
      (∑ g : Polynomial params, leftTensor (ι₂ := ι) (G * X g * X g * G)) ≤
        ∑ g : Polynomial params, leftTensor (ι₂ := ι) (G * X g * G) := by
    refine Finset.sum_le_sum ?_
    intro g _
    simpa [leftTensor, opTensor] using
      (opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
        (by simpa [mul_assoc] using MIPStarRE.Quantum.sandwich_mono hGherm (hXsq_le g))
        (show (0 : MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one))
  have hsumX : ∑ g : Polynomial params, X g = ∑ o : Outcome, Mo o * G * Mo o := by
    simpa [X, G, Mo] using switcherooAggregateFourthTermX_sum params family M q
  have hmid_le : ∑ o : Outcome, Mo o * G * Mo o ≤ 1 := by
    simpa [G, Mo] using switcherooAggregateFourthTerm_middle_sum_le_one params family M q
  have hsandwich_le : G * (∑ g : Polynomial params, X g) * G ≤ G := by
    calc
      G * (∑ g : Polynomial params, X g) * G ≤ G * 1 * G := by
        exact MIPStarRE.Quantum.sandwich_mono hGherm (by simpa [hsumX] using hmid_le)
      _ = G := by simp [hGsq]
  calc
    (∑ g : Polynomial params,
        (∑ o : Outcome,
            leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o)) *
          (∑ o : Outcome,
            leftTensor (ι₂ := ι)
              ((completePartSubMeas params family q.1).total *
                (M q.2).outcome o *
                (family.meas q.1).outcome g *
                (M q.2).outcome o))ᴴ)
      = ∑ g : Polynomial params, leftTensor (ι₂ := ι) (G * X g * X g * G) := by
          simpa [G, Gq, Mo] using hsum
    _ ≤ ∑ g : Polynomial params, leftTensor (ι₂ := ι) (G * X g * G) := hsandwichSum_le
    _ = leftTensor (ι₂ := ι) (G * (∑ g : Polynomial params, X g) * G) := by
          rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
            (fun g : Polynomial params => G * X g * G)]
          congr 1
          simp [mul_assoc, Matrix.mul_sum, Finset.sum_mul]
    _ ≤ leftTensor (ι₂ := ι) G := by
          simpa [leftTensor, opTensor] using
            (opTensor_mono_left (ι₂ := ι) (B := (1 : MIPStarRE.Quantum.Op ι))
              hsandwich_le (show (0 : MIPStarRE.Quantum.Op ι) ≤ 1 by exact zero_le_one))
    _ ≤ 1 := by
          simpa [G] using leftTensor_le_one (ι₂ := ι)
            ((completePartSubMeas params family q.1).total_le_one)

/-- The first `sqrt zeta` step in the fourth-term switcheroo chain. -/
lemma switcherooAggregateFourthTerm_once_commuted_close_mixed
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

end MIPStarRE.LDT.Pasting
