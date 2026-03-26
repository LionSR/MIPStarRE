import MIPStarRE.LDT.Preliminaries.Defs

/-!
Matching scaffold for Section 4 of the low individual degree paper in
`references/ldt-paper/preliminaries.tex`.

This file records the main proposition names with placeholder proofs.
-/

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:simeq-for-measurements`. The equivalence is definitional:
`agreementProbability = 1 - consistencyError`, so `consistencyError ≤ δ`
iff `agreementProbability ≥ 1 - δ`. -/
theorem simeqForMeasurements {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) (δ : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) δ ↔
      ConsistencyAsAgreement ψ 𝒟 A B δ := by
  unfold consistency ConsistencyAsAgreement agreementProbability
  constructor
  · intro ⟨h⟩
    exact ⟨by linarith⟩
  · intro ⟨h⟩
    exact ⟨by linarith⟩

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

/-! ### Bridge lemmas for `prop:cons-sub-meas`

The following three lemmas isolate the key mathematical steps of
Proposition 4.8: the inconsistency bound controls the diagonal
sandwich, the sandwich-to-total comparison, and the combination
via the triangle inequality for `≈_δ`. Full proofs require the
honest tensor-product API (tracked in the `TODO(tensor)` note in
`Defs.lean`). -/

/-- The off-diagonal mass bound controls the distance from `A` to
the diagonal sandwich `A_a B_a A_a`. -/
private lemma consSubMeas_diagonalControl
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) (γ : Error) :
    consistency ψ 𝒟 A
      (IndexedMeasurement.toIndexedSubMeasurement B) γ →
    StateDependentDistanceRel ψ 𝒟 A
      (diagonalSandwichFamily A B) γ := by
  sorry

/-- The off-diagonal mass bound controls the distance from the
diagonal sandwich `A_a B_a A_a` to the total sandwich
`A_a (Σ_b B_b) A_a`. -/
private lemma consSubMeas_sandwichControl
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) (γ : Error) :
    consistency ψ 𝒟 A
      (IndexedMeasurement.toIndexedSubMeasurement B) γ →
    StateDependentDistanceRel ψ 𝒟
      (diagonalSandwichFamily A B)
      (totalSandwichFamily A B) γ := by
  sorry

/-- Combined bound from the triangle inequality for `≈_δ`:
`dist(A, totalSandwich) ≤ 4γ`. The `4γ` arises because the paper's proof
of Prop 4.8 uses two applications of the triangle inequality, each contributing
a `2γ` bound (one from the diagonal control and one from the sandwich control).
The actual proof will need to show each `γ` input decomposes into a `2γ` bound. -/
private lemma consSubMeas_combinedControl
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) (γ : Error) :
    StateDependentDistanceRel ψ 𝒟 A
      (diagonalSandwichFamily A B) γ →
    StateDependentDistanceRel ψ 𝒟
      (diagonalSandwichFamily A B)
      (totalSandwichFamily A B) γ →
    StateDependentDistanceRel ψ 𝒟 A
      (totalSandwichFamily A B) (4 * γ) := by
  sorry

/-- `prop:cons-sub-meas`. -/
theorem consSubMeas {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) (γ : Error) :
    consistency ψ 𝒟 A
      (IndexedMeasurement.toIndexedSubMeasurement B) γ →
    ConsSubMeasStatement ψ 𝒟 A B γ := by
  intro hcons
  have hdc := consSubMeas_diagonalControl ψ 𝒟 A B γ hcons
  have hsc := consSubMeas_sandwichControl ψ 𝒟 A B γ hcons
  exact {
    diagonalControl := hdc
    sandwichControl := hsc
    combinedControl :=
      consSubMeas_combinedControl ψ 𝒟 A B γ hdc hsc
  }

/-! ### Bridge lemmas for `prop:switch-sandwich`

The following two lemmas isolate the key steps of Proposition 4.9:
moving one copy of `A_a^x` across the bipartition using the
`≈_δ` hypothesis, and using projectivity to collapse the
resulting sandwich. -/

/-- At scaffold level, `leftTensor` only changes the `name` field of an operator,
so the left and middle sandwich expectations are definitionally equal. -/
private lemma leftSandwich_eq_middleSandwich
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) :
    leftSandwichExpectation ψ 𝒟 A B = middleSandwichExpectation ψ 𝒟 A B := by
  unfold leftSandwichExpectation middleSandwichExpectation leftTensor
  rfl

/-- At scaffold level, `rightTensor` only changes the `name` field of an operator,
so the middle and right sandwich expectations are definitionally equal. -/
private lemma middleSandwich_eq_rightSandwich
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) :
    middleSandwichExpectation ψ 𝒟 A B = rightSandwichExpectation ψ 𝒟 A B := by
  unfold middleSandwichExpectation rightSandwichExpectation rightTensor
  rfl

/-- Moving one copy of `A_a^x` across the bipartition gives the
left sandwich transfer bound (error `2√δ`). At scaffold level this is
trivial because `leftTensor` is a name-only operation. -/
private lemma switchSandwich_leftTransfer
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) (hB : OperatorBetweenZeroAndOne B)
    (δ : Error) :
    bipartiteStateDependentDistance ψ 𝒟
      (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A)
      (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A)
      δ →
    |leftSandwichExpectation ψ 𝒟 A B -
      middleSandwichExpectation ψ 𝒟 A B| ≤
      2 * Real.sqrt δ := by
  intro _
  rw [leftSandwich_eq_middleSandwich, sub_self, abs_zero]
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg δ)

/-- Using projectivity `(A_a^x)² = A_a^x` to collapse the
sandwich gives the right transfer bound (error `√δ`). At scaffold level
this is trivial because `rightTensor` is a name-only operation. -/
private lemma switchSandwich_rightTransfer
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) (hB : OperatorBetweenZeroAndOne B)
    (δ : Error) :
    bipartiteStateDependentDistance ψ 𝒟
      (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A)
      (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A)
      δ →
    |middleSandwichExpectation ψ 𝒟 A B -
      rightSandwichExpectation ψ 𝒟 A B| ≤
      Real.sqrt δ := by
  intro _
  rw [middleSandwich_eq_rightSandwich, sub_self, abs_zero]
  exact Real.sqrt_nonneg δ

/-- `prop:switch-sandwich`. -/
theorem switchSandwich {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) (hB : OperatorBetweenZeroAndOne B)
    (δ : Error) :
    bipartiteStateDependentDistance ψ 𝒟
      (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A)
      (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A)
      δ →
    SwitchSandwichStatement ψ 𝒟 A B δ := by
  intro happrox
  exact {
    leftSandwichTransfer :=
      switchSandwich_leftTransfer ψ 𝒟 A B hB δ happrox
    rightSandwichTransfer :=
      switchSandwich_rightTransfer ψ 𝒟 A B hB δ happrox
  }

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

/-- `prop:completing-to-measurement`. The witness is the canonical completion
`completeAtOutcome B a0` which adds the residual `I - Σ_a B_a` to outcome `a0`. -/
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
  intro _hsc _hdist
  exact ⟨completeAtOutcome B a0, {
    completionFormula := rfl
    closenessAfterCompletion := by sorry
  }⟩

end MIPStarRE.LDT.Preliminaries
