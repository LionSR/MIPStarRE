import MIPStarRE.LDT.Preliminaries.Defs

/-!
Matching scaffold for Section 4 of the low individual degree paper in
`references/ldt-paper/preliminaries.tex`.

This file records the main proposition names with placeholder proofs.
-/

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-!
The two propositions below (`consSubMeas` and `switchSandwich`) are currently
provided through local axiomatizations matching the blueprint statements.
They can be replaced by concrete operator-level proofs once the bipartite
matrix API and the corresponding sandwich estimates are fully available.
-/

/-! ### Local axiom bridges for Section 4 sandwich statements -/

/-- Axiomatized bridge for `prop:cons-sub-meas`. -/
axiom consSubMeasCore {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) (γ : Error) :
    consistency ψ 𝒟 A (IndexedMeasurement.toIndexedSubMeasurement B) γ →
      ConsSubMeasStatement ψ 𝒟 A B γ

/-- Axiomatized bridge for `prop:switch-sandwich`. -/
axiom switchSandwichCore {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) (_hB : OperatorBetweenZeroAndOne B) (δ : Error) :
    bipartiteStateDependentDistance ψ 𝒟
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A)
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A) δ →
      SwitchSandwichStatement ψ 𝒟 A B δ

/-- `prop:simeq-for-measurements`. -/
theorem simeqForMeasurements {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) (δ : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) δ ↔
      ConsistencyAsAgreement ψ 𝒟 A B δ := by
  sorry

/-- `prop:simeq-to-approx`. -/
theorem simeqToApprox {Question Outcome : Type*}
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
theorem simeqDataProcessing {Question α β : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question α) (δ : Error) (f : α → β) :
    consistency ψ 𝒟 A B δ →
      consistency ψ 𝒟
        (postprocessIndexedSubMeasurement A f)
        (postprocessIndexedSubMeasurement B f) δ := by
  sorry

/-- `prop:cons-sub-meas`. -/
theorem consSubMeas {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) (γ : Error) :
    consistency ψ 𝒟 A (IndexedMeasurement.toIndexedSubMeasurement B) γ →
      ConsSubMeasStatement ψ 𝒟 A B γ := by
  exact consSubMeasCore ψ 𝒟 A B γ

/-- `prop:switch-sandwich`. -/
theorem switchSandwich {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) (_hB : OperatorBetweenZeroAndOne B) (δ : Error) :
    bipartiteStateDependentDistance ψ 𝒟
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A)
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A) δ →
      SwitchSandwichStatement ψ 𝒟 A B δ := by
  exact switchSandwichCore ψ 𝒟 A B _hB δ

/-- `prop:completeness-transfer-projective-P`. -/
theorem completenessTransferProjectiveP {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (P : IndexedProjectiveSubMeasurement Question Outcome) (ε : Error) :
    stateDependentDistance ψ 𝒟 A
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement P) ε →
      CompletenessTransferProjectivePStatement ψ 𝒟 A P ε := by
  sorry

/-- `prop:two-notions-of-self-consistency`. -/
theorem twoNotionsOfSelfConsistency {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) (δ : Error) :
    strongSelfConsistency ψ 𝒟 A δ →
      bipartiteStateDependentDistance ψ 𝒟 A A (2 * δ) := by
  sorry

/-- `prop:completing-to-measurement`. -/
theorem completingToMeasurement {Outcome : Type*}
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

end MIPStarRE.LDT.Preliminaries
