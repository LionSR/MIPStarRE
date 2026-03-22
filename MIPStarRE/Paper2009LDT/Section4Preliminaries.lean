import MIPStarRE.Paper2009LDT.Section3Test

/-!
Matching scaffold for Section 4 of the low individual degree paper in
`references/ldt-paper/preliminaries.tex`.

This file introduces lightweight paper-local definitions for the measurement
calculus of the paper and records the main proposition names with placeholder
proofs.
-/

namespace MIPStarRE.Paper2009LDT.Section4Preliminaries

open MIPStarRE.Paper2009LDT

/-- `def:post-processing` in `preliminaries.tex`. -/
def postProcessing {α β : Type _} (A : SubMeasurement α) (f : α → β) : SubMeasurement β :=
  postprocess A f

/-- `def:measurement-completion` in `preliminaries.tex`. -/
def measurementCompletion {α : Type _} (A : SubMeasurement α) : Measurement (Option α) :=
  completeSubMeasurement A

/-- `def:simeq` in `preliminaries.tex`. -/
def consistency {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (δ : Error) : Prop :=
  ConsistencyRel ψ 𝒟 A B δ

/-- `def:approx_delta` in `preliminaries.tex`. -/
def stateDependentDistance {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (δ : Error) : Prop :=
  StateDependentDistanceRel ψ 𝒟 A B δ

/-- `def:strong-self-consistency` in `preliminaries.tex`. -/
def strongSelfConsistency {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) (δ : Error) : Prop :=
  StrongSelfConsistencyRel ψ 𝒟 A δ

/-- Placeholder agreement probability from `prop:simeq-for-measurements`. -/
def agreementProbability {Question Outcome : Type _}
    (_ψ : QuantumState) (_𝒟 : Distribution Question)
    (_A _B : IndexedMeasurement Question Outcome) : Error := 0

/-- Output package for the measurement reformulation of consistency. -/
structure ConsistencyAsAgreement {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) (δ : Error) : Prop where
  agreementLowerBound : agreementProbability ψ 𝒟 A B ≥ 1 - δ

/-- Post-process an indexed family questionwise. -/
def postprocessIndexedSubMeasurement {Question α β : Type _}
    (A : IndexedSubMeasurement Question α) (f : α → β) :
    IndexedSubMeasurement Question β :=
  fun q => postProcessing (A q) f

/-- Placeholder family for the intermediate `A_a ⊗ B_a` sandwich. -/
def diagonalSandwichFamily {Question Outcome : Type _}
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) :
    IndexedSubMeasurement Question Outcome :=
  fun q => {
    name := s!"{(A q).name}.diagSandwich({(B q).toSubMeasurement.name})"
    outcomeOperator := fun _ => { name := s!"{(A q).name}.diagSandwich.outcome" }
    totalOperator := { name := s!"{(A q).name}.diagSandwich.total" }
  }

/-- Placeholder family for the intermediate `A ⊗ B_a` sandwich. -/
def totalSandwichFamily {Question Outcome : Type _}
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) :
    IndexedSubMeasurement Question Outcome :=
  fun q => {
    name := s!"{(A q).name}.totalSandwich({(B q).toSubMeasurement.name})"
    outcomeOperator := fun _ => { name := s!"{(A q).name}.totalSandwich.outcome" }
    totalOperator := { name := s!"{(A q).name}.totalSandwich.total" }
  }

/-- Output package for `prop:cons-sub-meas`. -/
structure ConsSubMeasStatement {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) (γ : Error) : Prop where
  diagonalControl :
    StateDependentDistanceRel ψ 𝒟 A (diagonalSandwichFamily A B) γ
  sandwichControl :
    StateDependentDistanceRel ψ 𝒟 (diagonalSandwichFamily A B) (totalSandwichFamily A B) γ
  combinedControl :
    StateDependentDistanceRel ψ 𝒟 A (totalSandwichFamily A B) (4 * γ)

/-- Placeholder scalar on the left-hand side of `prop:switch-sandwich`. -/
def leftSandwichExpectation {Question Outcome : Type _}
    (_ψ : QuantumState) (_𝒟 : Distribution Question)
    (_A : IndexedProjectiveSubMeasurement Question Outcome)
    (_B : Operator) : Error := 0

/-- Placeholder scalar for the middle term of `prop:switch-sandwich`. -/
def middleSandwichExpectation {Question Outcome : Type _}
    (_ψ : QuantumState) (_𝒟 : Distribution Question)
    (_A : IndexedProjectiveSubMeasurement Question Outcome)
    (_B : Operator) : Error := 0

/-- Placeholder scalar on the right-hand side of `prop:switch-sandwich`. -/
def rightSandwichExpectation {Question Outcome : Type _}
    (_ψ : QuantumState) (_𝒟 : Distribution Question)
    (_A : IndexedProjectiveSubMeasurement Question Outcome)
    (_B : Operator) : Error := 0

/-- Output package for `prop:switch-sandwich`. -/
structure SwitchSandwichStatement {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) (δ : Error) : Prop where
  leftSandwichTransfer :
    |leftSandwichExpectation ψ 𝒟 A B - middleSandwichExpectation ψ 𝒟 A B|
      ≤ 2 * Real.sqrt δ
  rightSandwichTransfer :
    |middleSandwichExpectation ψ 𝒟 A B - rightSandwichExpectation ψ 𝒟 A B|
      ≤ Real.sqrt δ

/-- Output package for `prop:completeness-transfer-projective-P`. -/
structure CompletenessTransferProjectivePStatement {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (P : IndexedProjectiveSubMeasurement Question Outcome) (ε : Error) : Prop where
  completenessTransfer :
    indexedSubMeasurementMass ψ 𝒟 A ≥
      indexedSubMeasurementMass ψ 𝒟
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement P)
        - 2 * Real.sqrt ε

/-- Canonical completion of `B` by adjoining the failure mass to the distinguished outcome `a0`. -/
noncomputable def completeAtOutcome {Outcome : Type _}
    (B : SubMeasurement Outcome) (a0 : Outcome) : Measurement Outcome := by
  classical
  refine {
    toSubMeasurement := {
      name := s!"{B.name}.completed"
      outcomeOperator := fun a =>
        if h : a = a0 then
          { name := s!"{B.name}.completed.main" }
        else
          B.outcomeOperator a
      totalOperator := { name := s!"{B.name}.completed.total" }
    }
  }

/-- Output package for `prop:completing-to-measurement`. -/
structure CompletingToMeasurementStatement {Outcome : Type _}
    (ψ : QuantumState)
    (A : Measurement Outcome) (B : SubMeasurement Outcome)
    (C : Measurement Outcome) (a0 : Outcome) (δ ζ : Error) : Prop where
  completionFormula : C = completeAtOutcome B a0
  closenessAfterCompletion :
    StateDependentDistanceRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily A.toSubMeasurement)
      (constantSubMeasurementFamily C.toSubMeasurement)
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ)

/-- `prop:simeq-for-measurements`. -/
theorem simeqForMeasurements {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) (δ : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) δ ↔
      ConsistencyAsAgreement ψ 𝒟 A B δ := by
  sorry

/-- `prop:simeq-to-approx`. -/
theorem simeqToApprox {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) (δ : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) δ →
      stateDependentDistance ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) (2 * δ) := by
  sorry

/-- `prop:simeq-data-processing`. -/
theorem simeqDataProcessing {Question α β : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question α) (δ : Error) (f : α → β) :
    consistency ψ 𝒟 A B δ →
      consistency ψ 𝒟 (postprocessIndexedSubMeasurement A f)
        (postprocessIndexedSubMeasurement B f) δ := by
  sorry

/-- `prop:cons-sub-meas`. -/
theorem consSubMeas {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) (γ : Error) :
    consistency ψ 𝒟 A (IndexedMeasurement.toIndexedSubMeasurement B) γ →
      ConsSubMeasStatement ψ 𝒟 A B γ := by
  sorry

/-- `prop:switch-sandwich`. -/
theorem switchSandwich {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) (δ : Error) :
    stateDependentDistance ψ 𝒟
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A)
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A) δ →
      SwitchSandwichStatement ψ 𝒟 A B δ := by
  sorry

/-- `prop:completeness-transfer-projective-P`. -/
theorem completenessTransferProjectiveP {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (P : IndexedProjectiveSubMeasurement Question Outcome) (ε : Error) :
    stateDependentDistance ψ 𝒟 A
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement P) ε →
      CompletenessTransferProjectivePStatement ψ 𝒟 A P ε := by
  sorry

/-- `prop:two-notions-of-self-consistency`. -/
theorem twoNotionsOfSelfConsistency {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) (δ : Error) :
    strongSelfConsistency ψ 𝒟 A δ →
      stateDependentDistance ψ 𝒟 A A (2 * δ) := by
  sorry

/-- `prop:completing-to-measurement`. -/
theorem completingToMeasurement {Outcome : Type _}
    (ψ : QuantumState)
    (A : Measurement Outcome) (B : SubMeasurement Outcome)
    (a0 : Outcome) (δ ζ : Error) :
    strongSelfConsistency ψ (uniformDistribution Unit)
        (constantSubMeasurementFamily A.toSubMeasurement) ζ →
      stateDependentDistance ψ (uniformDistribution Unit)
        (constantSubMeasurementFamily A.toSubMeasurement)
        (constantSubMeasurementFamily B) δ →
      ∃ C : Measurement Outcome,
        CompletingToMeasurementStatement ψ A B C a0 δ ζ := by
  sorry

end MIPStarRE.Paper2009LDT.Section4Preliminaries
