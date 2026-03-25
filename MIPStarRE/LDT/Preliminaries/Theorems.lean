import MIPStarRE.LDT.Preliminaries.Defs

/-!
Matching scaffold for Section 4 of the low individual degree paper in
`references/ldt-paper/preliminaries.tex`.

This file records the main proposition names with placeholder proofs.
-/

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

private axiom simeqToApproxCore {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) (δ : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) δ →
      bipartiteStateDependentDistance ψ 𝒟
        (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B)
        (2 * δ)

private axiom simeqDataProcessingCore {Question α β : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question α) (δ : Error) (f : α → β) :
    consistency ψ 𝒟 A B δ →
      consistency ψ 𝒟
        (postprocessIndexedSubMeasurement A f)
        (postprocessIndexedSubMeasurement B f) δ

private axiom triangleInequalityForApproxDeltaCore {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B C : IndexedSubMeasurement Question Outcome) (δ₁ δ₂ : Error) :
    stateDependentDistance ψ 𝒟 A B δ₁ →
      stateDependentDistance ψ 𝒟 B C δ₂ →
        stateDependentDistance ψ 𝒟 A C (δ₁ + δ₂)

private axiom closenessOfIpCore {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (γ : Error) :
    stateDependentDistance ψ 𝒟 A B γ →
      |indexedSubMeasurementMass ψ 𝒟 A - indexedSubMeasurementMass ψ 𝒟 B| ≤ Real.sqrt γ

private axiom triangleSubCore {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome)
    (C : IndexedSubMeasurement Question Outcome) (δ ε : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A) C δ →
      bipartiteStateDependentDistance ψ 𝒟
        (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) ε →
        consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement B) C (δ + Real.sqrt ε)

private axiom simeqTriangleInequalityCore {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B C D : IndexedMeasurement Question Outcome) (ε δ γ : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) ε →
      consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement C)
        (IndexedMeasurement.toIndexedSubMeasurement B) δ →
      consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement C)
        (IndexedMeasurement.toIndexedSubMeasurement D) γ →
      consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement D)
        (ε + 2 * Real.sqrt (δ + γ))

/-- `prop:simeq-for-measurements`. -/
theorem simeqForMeasurements {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) (δ : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) δ ↔
      ConsistencyAsAgreement ψ 𝒟 A B δ := by
  constructor
  · intro h
    refine ⟨?_⟩
    unfold agreementProbability
    linarith [h.offDiagonalBound]
  · intro h
    refine ⟨?_⟩
    have h' := h.agreementLowerBound
    unfold agreementProbability at h'
    linarith

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
  exact simeqToApproxCore ψ 𝒟 A B δ

/-- `prop:simeq-data-processing`. -/
theorem simeqDataProcessing {Question α β : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question α) (δ : Error) (f : α → β) :
    consistency ψ 𝒟 A B δ →
      consistency ψ 𝒟
        (postprocessIndexedSubMeasurement A f)
        (postprocessIndexedSubMeasurement B f) δ := by
  exact simeqDataProcessingCore ψ 𝒟 A B δ f

/-- `prop:triangle-inequality-for-vectors-squared` in scalar form. -/
theorem triangleInequalityForVectorsSquared {ι : Type*} [Fintype ι]
    (v : ι → ℝ) :
    (∑ i, v i) ^ 2 ≤ Fintype.card ι * ∑ i, (v i) ^ 2 := by
  simpa [pow_two] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := v)

/-- `prop:triangle-inequality-for-approx_delta`. -/
theorem triangleInequalityForApproxDelta {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B C : IndexedSubMeasurement Question Outcome) (δ₁ δ₂ : Error) :
    stateDependentDistance ψ 𝒟 A B δ₁ →
      stateDependentDistance ψ 𝒟 B C δ₂ →
        stateDependentDistance ψ 𝒟 A C (δ₁ + δ₂) := by
  exact triangleInequalityForApproxDeltaCore ψ 𝒟 A B C δ₁ δ₂

/-- `prop:closeness-of-ip`. -/
theorem closenessOfIp {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (γ : Error) :
    stateDependentDistance ψ 𝒟 A B γ →
      |indexedSubMeasurementMass ψ 𝒟 A - indexedSubMeasurementMass ψ 𝒟 B| ≤ Real.sqrt γ := by
  exact closenessOfIpCore ψ 𝒟 A B γ

/-- `prop:triangle-sub`. -/
theorem triangleSub {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome)
    (C : IndexedSubMeasurement Question Outcome) (δ ε : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A) C δ →
      bipartiteStateDependentDistance ψ 𝒟
        (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) ε →
        consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement B) C (δ + Real.sqrt ε) := by
  exact triangleSubCore ψ 𝒟 A B C δ ε

/-- `prop:simeq-triangle-inequality`. -/
theorem simeqTriangleInequality {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B C D : IndexedMeasurement Question Outcome) (ε δ γ : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) ε →
      consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement C)
        (IndexedMeasurement.toIndexedSubMeasurement B) δ →
      consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement C)
        (IndexedMeasurement.toIndexedSubMeasurement D) γ →
      consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement D)
        (ε + 2 * Real.sqrt (δ + γ)) := by
  exact simeqTriangleInequalityCore ψ 𝒟 A B C D ε δ γ

/-- `prop:cons-sub-meas`. -/
theorem consSubMeas {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) (γ : Error) :
    consistency ψ 𝒟 A (IndexedMeasurement.toIndexedSubMeasurement B) γ →
      ConsSubMeasStatement ψ 𝒟 A B γ := by
  sorry

/-- `prop:switch-sandwich`. -/
theorem switchSandwich {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) (_hB : OperatorBetweenZeroAndOne B) (δ : Error) :
    bipartiteStateDependentDistance ψ 𝒟
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A)
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A) δ →
      SwitchSandwichStatement ψ 𝒟 A B δ := by
  sorry

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
