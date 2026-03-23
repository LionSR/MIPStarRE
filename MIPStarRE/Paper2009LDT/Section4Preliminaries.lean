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
noncomputable def postProcessing {α β : Type _} (A : SubMeasurement α) (f : α → β) :
    SubMeasurement β :=
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
  PermutationInvariantState ψ ∧ StrongSelfConsistencyRel ψ 𝒟 A δ

/-- Source-style left/right relation `A^x_a ⊗ I ≈_δ I ⊗ B^x_a`.

TODO(tensor): this currently reuses the single-register comparison layer from Section 3,
so users should wrap `A` and `B` in the local `leftTensor` / `rightTensor` placements
before invoking it. Replacing this by an honest tensor-product API remains future work.
-/
structure BipartiteStateDependentDistanceRel {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (δ : Error) : Prop where
  leftRightSquaredDistanceBound : stateDependentDistanceError ψ 𝒟 A B ≤ δ

/-- Abbreviation for the bipartite state-dependent distance used in the source propositions. -/
def bipartiteStateDependentDistance {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (δ : Error) : Prop :=
  BipartiteStateDependentDistanceRel ψ 𝒟 A B δ

/-- Condition `0 ≤ B ≤ I` for the switch-sandwich argument, with the identity taken in
`B`'s ambient dimension. -/
structure OperatorBetweenZeroAndOne (B : Operator) : Prop where
  nonnegative : PositiveSemidefinite B
  boundedByIdentity : DominatesOperator (identityLike B) B

/-- Placeholder agreement probability from `prop:simeq-for-measurements`. -/
noncomputable def agreementProbability {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) : Error :=
  1 - consistencyError ψ 𝒟
        (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B)

/-- Output package for the measurement reformulation of consistency. -/
structure ConsistencyAsAgreement {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) (δ : Error) : Prop where
  agreementLowerBound : agreementProbability ψ 𝒟 A B ≥ 1 - δ

/-- Post-process an indexed family questionwise. -/
noncomputable def postprocessIndexedSubMeasurement {Question α β : Type _}
    (A : IndexedSubMeasurement Question α) (f : α → β) :
    IndexedSubMeasurement Question β :=
  fun q => postProcessing (A q) f

/-- The completion residual `I - Σ_a B_a` used when completing a submeasurement. -/
noncomputable def completionResidualOperator {Outcome : Type _} (B : SubMeasurement Outcome) : Operator :=
  operatorDifference (identityLike B.totalOperator) B.totalOperator

/-- Family for the intermediate `A_a B_a A_a` sandwich. -/
noncomputable def diagonalSandwichFamily {Question Outcome : Type _}
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) :
    IndexedSubMeasurement Question Outcome :=
  fun q => {
    name := s!"{(A q).name}.diagSandwich({(B q).toSubMeasurement.name})"
    outcomeOperator := fun a =>
      operatorSandwich
        ((A q).outcomeOperator a)
        ((B q).toSubMeasurement.outcomeOperator a)
        ((A q).outcomeOperator a)
    totalOperator := (A q).totalOperator
  }

/-- Family for the intermediate `A_a (Σ_b B_b) A_a` sandwich. -/
noncomputable def totalSandwichFamily {Question Outcome : Type _}
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) :
    IndexedSubMeasurement Question Outcome :=
  fun q => {
    name := s!"{(A q).name}.totalSandwich({(B q).toSubMeasurement.name})"
    outcomeOperator := fun a =>
      operatorSandwich
        ((A q).outcomeOperator a)
        (B q).toSubMeasurement.totalOperator
        ((A q).outcomeOperator a)
    totalOperator := (A q).totalOperator
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

/-- Averaged left-placed sandwich scalar from `prop:switch-sandwich`. -/
noncomputable def leftSandwichExpectation {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) : Error :=
  averageOverDistribution 𝒟 fun q =>
    expectationValue ψ <|
      operatorSandwich
        ((A q).toSubMeasurement.totalOperator)
        (leftTensor B)
        ((A q).toSubMeasurement.totalOperator)

/-- Averaged middle sandwich scalar from `prop:switch-sandwich`. -/
noncomputable def middleSandwichExpectation {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) : Error :=
  averageOverDistribution 𝒟 fun q =>
    expectationValue ψ <|
      operatorSandwich
        ((A q).toSubMeasurement.totalOperator)
        B
        ((A q).toSubMeasurement.totalOperator)

/-- Averaged right-placed sandwich scalar from `prop:switch-sandwich`. -/
noncomputable def rightSandwichExpectation {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) : Error :=
  averageOverDistribution 𝒟 fun q =>
    expectationValue ψ <|
      operatorSandwich
        ((A q).toSubMeasurement.totalOperator)
        (rightTensor B)
        ((A q).toSubMeasurement.totalOperator)

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

/-- Canonical completion of `B` by adjoining the residual `I - Σ_a B_a` to the distinguished outcome `a0`. -/
noncomputable def completeAtOutcome {Outcome : Type _}
    (B : SubMeasurement Outcome) (a0 : Outcome) : Measurement Outcome := by
  classical
  let residual := completionResidualOperator B
  refine {
    toSubMeasurement := {
      name := s!"{B.name}.completed"
      outcomeOperator := fun a =>
        if h : a = a0 then
          operatorAdd (B.outcomeOperator a) residual
        else
          B.outcomeOperator a
      totalOperator := identityLike B.totalOperator
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
      bipartiteStateDependentDistance ψ 𝒟
        (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B)
        (2 * δ) := by
  sorry

/-- `prop:simeq-data-processing`. -/
theorem simeqDataProcessing {Question α β : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question α) (δ : Error) (f : α → β) :
    consistency ψ 𝒟 A B δ →
      consistency ψ 𝒟
        (postprocessIndexedSubMeasurement A f)
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
    (B : Operator) (_hB : OperatorBetweenZeroAndOne B) (δ : Error) :
    bipartiteStateDependentDistance ψ 𝒟
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
      bipartiteStateDependentDistance ψ 𝒟 A A (2 * δ) := by
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
