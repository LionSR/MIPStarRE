import MIPStarRE.LDT.Test.MainTheorem

/-!
Matching scaffold for Section 4 of the low individual degree paper in
`references/ldt-paper/preliminaries.tex`.

This file introduces lightweight paper-local definitions for the measurement
calculus of the paper. All operator fields use `Op ι` directly.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT
open MIPStarRE.Quantum

/-- Source-style left/right relation `A^x_a ⊗ I ≈_δ I ⊗ B^x_a`. -/
structure BipartiteSDDRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  leftRightSquaredDistanceBound :
    sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftRight B) ≤ δ

/-- Condition `0 ≤ B ≤ I` for the switch-sandwich argument. -/
structure OpBounded01 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : MIPStarRE.Quantum.Op ι) : Prop where
  nonnegative : 0 ≤ B
  boundedByIdentity : 0 ≤ (1 : MIPStarRE.Quantum.Op ι) - B

/-- Placeholder agreement probability from `prop:simeq-for-measurements`. -/
noncomputable def agreementProbability {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome ι) : Error :=
  1 - consError ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B)

/-- Output package for the measurement reformulation of consistency. -/
structure ConsAgreement {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome ι) (δ : Error) : Prop where
  agreementLowerBound : agreementProbability ψ 𝒟 A B ≥ 1 - δ

-- `leftTensor_mul_rightTensor_eq_opTensor` is now in `Basic/Operator.lean`
-- (namespace `MIPStarRE.LDT`). We re-export for backwards compatibility.
-- Local alias removed per PR review to avoid duplication.

/-- `A_a ⊗ B_a`, the diagonal bipartite bridge from `prop:cons-sub-meas`. -/
noncomputable def diagonalSandwichFamily {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome (ι × ι) :=
  fun q => {
    outcome := fun a =>
      leftTensor (ι₂ := ι) ((A q).outcome a) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    total := ∑ a : Outcome,
      leftTensor (ι₂ := ι) ((A q).outcome a) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    outcome_pos := by
      intro a
      rw [leftTensor_mul_rightTensor_eq_opTensor]
      exact
        (Matrix.PosSemidef.kronecker
          (Matrix.nonneg_iff_posSemidef.mp ((A q).outcome_pos a))
          (Matrix.nonneg_iff_posSemidef.mp ((B q).outcome_pos a))).nonneg
    sum_eq_total := by
      rfl
    total_le_one := by
      calc
        ∑ a : Outcome,
            leftTensor (ι₂ := ι) ((A q).outcome a) *
              rightTensor (ι₁ := ι) ((B q).outcome a)
          ≤ ∑ a : Outcome, leftTensor (ι₂ := ι) ((A q).outcome a) := by
              refine Finset.sum_le_sum ?_
              intro a ha
              have hopTensor_le :
                  opTensor ((A q).outcome a) ((B q).outcome a) ≤
                    leftTensor (ι₂ := ι) ((A q).outcome a) := by
                change
                  (leftTensor (ι₂ := ι) ((A q).outcome a) -
                    opTensor ((A q).outcome a) ((B q).outcome a)).PosSemidef
                have hrewrite :
                    leftTensor (ι₂ := ι) ((A q).outcome a) -
                      opTensor ((A q).outcome a) ((B q).outcome a) =
                    opTensor ((A q).outcome a) (1 - (B q).outcome a) := by
                  have hneg :
                      Matrix.kronecker ((A q).outcome a) (-((B q).outcome a)) =
                        -Matrix.kronecker ((A q).outcome a) ((B q).outcome a) := by
                    simpa using
                      (Matrix.kronecker_smul (-1 : ℂ) ((A q).outcome a) ((B q).outcome a))
                  calc
                    leftTensor (ι₂ := ι) ((A q).outcome a) -
                        opTensor ((A q).outcome a) ((B q).outcome a)
                      =
                        Matrix.kronecker ((A q).outcome a) 1 +
                          Matrix.kronecker ((A q).outcome a) (-((B q).outcome a)) := by
                            rw [hneg]
                            simp [leftTensor, opTensor, sub_eq_add_neg]
                    _ = Matrix.kronecker ((A q).outcome a) (1 - (B q).outcome a) := by
                          simpa [sub_eq_add_neg] using
                            (Matrix.kronecker_add ((A q).outcome a) 1 (-((B q).outcome a))).symm
                    _ = opTensor ((A q).outcome a) (1 - (B q).outcome a) := by
                          simp [opTensor]
                have hpsd :
                    Matrix.PosSemidef
                      (opTensor ((A q).outcome a) (1 - (B q).outcome a)) := by
                  change
                    Matrix.PosSemidef
                      (Matrix.kronecker ((A q).outcome a) (1 - (B q).outcome a))
                  exact
                    Matrix.PosSemidef.kronecker
                      (Matrix.nonneg_iff_posSemidef.mp ((A q).outcome_pos a))
                      (Matrix.nonneg_iff_posSemidef.mp
                        (sub_nonneg.mpr (Measurement.outcome_le_one (B q) a)))
                rwa [hrewrite]
              rw [leftTensor_mul_rightTensor_eq_opTensor]
              exact hopTensor_le
        _ = leftTensor (ι₂ := ι) ((A q).total) := by
          rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun a => (A q).outcome a)]
          rw [(A q).sum_eq_total]
        _ ≤ 1 := leftTensor_le_one (ι₂ := ι) (A q).total_le_one
  }

/-- `A ⊗ B_a`, the total bipartite bridge from `prop:cons-sub-meas`. -/
noncomputable def totalSandwichFamily {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome (ι × ι) :=
  fun q => {
    outcome := fun a =>
      leftTensor (ι₂ := ι) ((A q).total) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    total := ∑ a : Outcome,
      leftTensor (ι₂ := ι) ((A q).total) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    outcome_pos := by
      intro a
      rw [leftTensor_mul_rightTensor_eq_opTensor]
      exact
        (Matrix.PosSemidef.kronecker
          (Matrix.nonneg_iff_posSemidef.mp (SubMeas.total_nonneg (A q)))
          (Matrix.nonneg_iff_posSemidef.mp ((B q).outcome_pos a))).nonneg
    sum_eq_total := by
      rfl
    total_le_one := by
      calc
        ∑ a : Outcome,
            leftTensor (ι₂ := ι) ((A q).total) *
              rightTensor (ι₁ := ι) ((B q).outcome a)
          = leftTensor (ι₂ := ι) ((A q).total) := by
              rw [← Finset.mul_sum]
              rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ (fun a => (B q).outcome a)]
              rw [(B q).sum_eq]
              simp [leftTensor, rightTensor]
        _ ≤ 1 := leftTensor_le_one (ι₂ := ι) (A q).total_le_one
  }

/-- Output package for `prop:cons-sub-meas`. -/
structure ConsSubMeasStmt {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) : Prop where
  diagonalControl :
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (diagonalSandwichFamily A B) γ
  sandwichControl :
    SDDRel ψ 𝒟 (diagonalSandwichFamily A B) (totalSandwichFamily A B) γ
  combinedControl :
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (totalSandwichFamily A B) (4 * γ)

/-- Averaged left term `E_x ∑_a ⟨ψ, (A_a B A_a ⊗ I) ψ⟩`. -/
noncomputable def leftSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) : Error :=
  avgOver 𝒟 fun q =>
    ∑ a, ev ψ
      (leftTensor (ι₂ := ι) ((A q).outcome a) *
        leftTensor (ι₂ := ι) B *
        leftTensor (ι₂ := ι) ((A q).outcome a))

/-- Averaged middle term `E_x ∑_a ⟨ψ, (B ⊗ A_a) ψ⟩`. -/
noncomputable def middleSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) : Error :=
  avgOver 𝒟 fun q =>
    ∑ a, ev ψ
      (leftTensor (ι₂ := ι) B *
        rightTensor (ι₁ := ι) ((A q).outcome a))

/-- Averaged right term `E_x ∑_a ⟨ψ, (B A_a ⊗ I) ψ⟩`. -/
noncomputable def rightSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) : Error :=
  avgOver 𝒟 fun q =>
    ∑ a, ev ψ
      (leftTensor (ι₂ := ι) (B * (A q).outcome a))

/-- Output package for `prop:switch-sandwich`. -/
structure SwitchSandwichStmt {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (δ : Error) : Prop where
  leftSandwichTransfer :
    |leftSandwichExpectation ψ 𝒟 A B -
      middleSandwichExpectation ψ 𝒟 A B|
      ≤ 2 * Real.sqrt δ
  rightSandwichTransfer :
    |middleSandwichExpectation ψ 𝒟 A B -
      rightSandwichExpectation ψ 𝒟 A B|
      ≤ Real.sqrt δ

/-- Output package for `prop:completeness-transfer-projective-P`. -/
structure CompTransferStmt {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (P : IdxProjSubMeas Question Outcome ι) (ε : Error) : Prop where
  completenessTransfer :
    idxSubMeasMass ψ 𝒟 A ≥
      idxSubMeasMass ψ 𝒟
        (IdxProjSubMeas.toIdxSubMeas P)
        - 2 * Real.sqrt ε

/-- Canonical completion of `B` by adjoining the residual `I - Σ_a B_a`
to the distinguished outcome `a0`. -/
noncomputable def completeAtOutcome {Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (B : SubMeas Outcome ι) (a0 : Outcome) : Measurement Outcome ι := by
  classical
  let residual := 1 - B.total
  exact {
    toSubMeas := {
      outcome := fun a =>
        if h : a = a0 then
          B.outcome a + residual
        else
          B.outcome a
      total := 1
      outcome_pos := by
        intro a
        by_cases h : a = a0
        · simpa [h, residual] using
            add_nonneg (B.outcome_pos a0) (sub_nonneg.mpr B.total_le_one)
        · simp [h, B.outcome_pos a]
      sum_eq_total := by
        have hsingle :
            (∑ x : Outcome, if x = a0 then residual else 0) = residual := by
          simp
        have hrewrite :
            (∑ a : Outcome, if h : a = a0 then B.outcome a + residual else B.outcome a) =
              ∑ a : Outcome, (B.outcome a + if a = a0 then residual else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a = a0 <;> simp [h]
        rw [hrewrite, Finset.sum_add_distrib, B.sum_eq_total, hsingle]
        simp [residual]
      total_le_one := le_rfl
    }
    total_eq_one := rfl
  }

/-- Output package for `prop:completing-to-measurement`. -/
structure CompletingToMeasStmt {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : Measurement Outcome ι) (B : SubMeas Outcome ι)
    (C : Measurement Outcome ι) (a0 : Outcome) (δ ζ : Error) : Prop where
  completionFormula : C = completeAtOutcome B a0
  closenessAfterCompletion :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily C.toSubMeas.liftLeft)
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ)

end MIPStarRE.LDT.Preliminaries
