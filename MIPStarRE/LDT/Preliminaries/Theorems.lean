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
  unfold consistency
  constructor
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability; linarith⟩
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability at h; linarith⟩

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

/-! ### Infrastructure: triangle inequality for `StateDependentDistanceRel`

The squared-norm triangle inequality `‖u+v‖² ≤ 2(‖u‖² + ‖v‖²)` lifts to a
triangle inequality for state-dependent distance: if `A ≈_δ₁ B` and
`B ≈_δ₂ C`, then `A ≈_{2(δ₁+δ₂)} C`. This requires operator algebra
infrastructure (matrix PSD inequalities) that the scaffold does not yet
provide. -/

/-- Triangle inequality for state-dependent distance. Requires proving
`‖(A_a-C_a)|ψ⟩‖² ≤ 2(‖(A_a-B_a)|ψ⟩‖² + ‖(B_a-C_a)|ψ⟩‖²)` at the
operator algebra level. -/
private lemma stateDependentDistanceRel_triangle
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B C : IndexedSubMeasurement Question Outcome) (δ₁ δ₂ : Error) :
    StateDependentDistanceRel ψ 𝒟 A B δ₁ →
    StateDependentDistanceRel ψ 𝒟 B C δ₂ →
    StateDependentDistanceRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) := by
  sorry

/-- Monotonicity: if `StateDependentDistanceRel` holds for `δ`,
it holds for any `δ' ≥ δ`. -/
private lemma stateDependentDistanceRel_mono
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (δ δ' : Error)
    (hle : δ ≤ δ') :
    StateDependentDistanceRel ψ 𝒟 A B δ →
    StateDependentDistanceRel ψ 𝒟 A B δ' := by
  intro ⟨h⟩
  exact ⟨le_trans h hle⟩

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
`dist(A, totalSandwich) ≤ 4γ`. Applies the triangle inequality
`A ≈_{2(γ+γ)} totalSandwich` and simplifies `2(γ+γ) = 4γ`. -/
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
  intro hAD hDT
  have h := stateDependentDistanceRel_triangle ψ 𝒟 A
    (diagonalSandwichFamily A B) (totalSandwichFamily A B) γ γ hAD hDT
  exact stateDependentDistanceRel_mono ψ 𝒟 A (totalSandwichFamily A B)
    (2 * (γ + γ)) (4 * γ) (by linarith) h

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

/-- `expectationValue` depends only on `dim` and `matrix`, not on `name`. -/
private lemma expectationValue_name_irrel (ψ : QuantumState)
    (n₁ n₂ : String) (d : ℕ) (m : MIPStarRE.Quantum.Op (HilbertIndex d)) :
    expectationValue ψ ⟨n₁, d, m⟩ = expectationValue ψ ⟨n₂, d, m⟩ := rfl

/-- At scaffold level, `leftTensor` only changes the `name` field of an operator,
so the left and middle sandwich expectations are equal. -/
private lemma leftSandwich_eq_middleSandwich
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) :
    leftSandwichExpectation ψ 𝒟 A B = middleSandwichExpectation ψ 𝒟 A B := by
  unfold leftSandwichExpectation middleSandwichExpectation leftTensor
  congr 1; funext q; rcases B with ⟨_, d, m⟩
  unfold operatorSandwich
  split <;> (try split) <;> exact expectationValue_name_irrel ψ _ _ _ _

/-- At scaffold level, `rightTensor` only changes the `name` field of an operator,
so the middle and right sandwich expectations are equal. -/
private lemma middleSandwich_eq_rightSandwich
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) :
    middleSandwichExpectation ψ 𝒟 A B = rightSandwichExpectation ψ 𝒟 A B := by
  unfold middleSandwichExpectation rightSandwichExpectation rightTensor
  congr 1; funext q; rcases B with ⟨_, d, m⟩
  unfold operatorSandwich
  split <;> (try split) <;> exact expectationValue_name_irrel ψ _ _ _ _

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

/-- `prop:two-notions-of-self-consistency`. Requires showing
`stateDependentDistanceError A A ≤ 2 * strongSelfConsistencyError A`
via the expansion `‖(A_a ⊗ I - I ⊗ A_a)|ψ⟩‖²` and comparison with the
diagonal overlap in the strong self-consistency definition. -/
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
