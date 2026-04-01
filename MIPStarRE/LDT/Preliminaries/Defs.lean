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

/-- Source-style left/right relation `A^x_a ⊗ I ≈_δ I ⊗ B^x_a`. -/
structure BipartiteSDDRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  leftRightSquaredDistanceBound : sddError ψ 𝒟 A B ≤ δ

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

/-- Family for the intermediate `A_a B_a A_a` sandwich. -/
noncomputable def diagonalSandwichFamily {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => {
    outcome := fun a =>
      (A q).outcome a * (B q).toSubMeas.outcome a * (A q).outcome a
    total := ∑ a : Outcome,
      (A q).outcome a * (B q).toSubMeas.outcome a * (A q).outcome a
    outcome_pos := by
      intro a
      sorry
    sum_eq_total := by
      rfl
    total_le_one := by
      sorry
  }

/-- Family for the intermediate `A_a (Σ_b B_b) A_a` sandwich. -/
noncomputable def totalSandwichFamily {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => {
    outcome := fun a =>
      (A q).outcome a * (B q).toSubMeas.total * (A q).outcome a
    total := ∑ a : Outcome,
      (A q).outcome a * (B q).toSubMeas.total * (A q).outcome a
    outcome_pos := by
      intro a
      sorry
    sum_eq_total := by
      rfl
    total_le_one := by
      sorry
  }

/-- Output package for `prop:cons-sub-meas`. -/
structure ConsSubMeasStmt {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) : Prop where
  diagonalControl :
    SDDRel ψ 𝒟 A (diagonalSandwichFamily A B) γ
  sandwichControl :
    SDDRel ψ 𝒟 (diagonalSandwichFamily A B) (totalSandwichFamily A B) γ
  combinedControl :
    SDDRel ψ 𝒟 A (totalSandwichFamily A B) (4 * γ)

/-- Averaged left-placed sandwich scalar from `prop:switch-sandwich`. -/
noncomputable def leftSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) : Error :=
  avgOver 𝒟 fun q =>
    ev ψ <|
      leftTensor (ι₂ := ι) (A q).toSubMeas.total *
        leftTensor (ι₂ := ι) B *
        leftTensor (ι₂ := ι) (A q).toSubMeas.total

/-- Averaged middle sandwich scalar from `prop:switch-sandwich`. -/
noncomputable def middleSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op (ι × ι)) : Error :=
  avgOver 𝒟 fun q =>
    ev ψ <|
      leftTensor (ι₂ := ι) (A q).toSubMeas.total *
        B *
        leftTensor (ι₂ := ι) (A q).toSubMeas.total

/-- Averaged right-placed sandwich scalar from `prop:switch-sandwich`. -/
noncomputable def rightSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) : Error :=
  avgOver 𝒟 fun q =>
    ev ψ <|
      leftTensor (ι₂ := ι) (A q).toSubMeas.total *
        rightTensor (ι₁ := ι) B *
        leftTensor (ι₂ := ι) (A q).toSubMeas.total

/-- Output package for `prop:switch-sandwich`. -/
structure SwitchSandwichStmt {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (δ : Error) : Prop where
  leftSandwichTransfer :
    |leftSandwichExpectation ψ 𝒟 A B -
      middleSandwichExpectation ψ 𝒟 A (leftTensor (ι₂ := ι) B)|
      ≤ 2 * Real.sqrt δ
  rightSandwichTransfer :
    |middleSandwichExpectation ψ 𝒟 A (rightTensor (ι₁ := ι) B) -
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
          simpa using
            (Finset.sum_ite_eq (s := Finset.univ) (a := a0) (b := residual))
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
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (B : SubMeas Outcome ι)
    (C : Measurement Outcome ι) (a0 : Outcome) (δ ζ : Error) : Prop where
  completionFormula : C = completeAtOutcome B a0
  closenessAfterCompletion :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily C.toSubMeas)
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ)

end MIPStarRE.LDT.Preliminaries
