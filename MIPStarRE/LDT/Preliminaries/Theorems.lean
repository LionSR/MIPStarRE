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

/-- Atomic mathematical fact: for a full measurement (`Σ A_a = I`),
the squared-distance defect `∑_a E[(A_a-B_a)†(A_a-B_a)]` is at most
`2 * questionConsistencyDefect`. This requires measurement completeness
(not yet enforced by the scaffold `Measurement` type) and the expansion
`‖A_a - B_a‖² = E[A_a²] + E[B_a²] - E[A_a B_a] - E[B_a A_a]`
combined with `Σ_a E[A_a²] ≤ Σ_a E[A_a] = 1`. -/
private lemma questionSDD_le_two_questionConsistency {Outcome : Type*}
    (ψ : QuantumState) (A B : Measurement Outcome) :
    questionStateDependentDistanceDefect ψ A.toSubMeasurement B.toSubMeasurement ≤
      2 * questionConsistencyDefect ψ A.toSubMeasurement B.toSubMeasurement := by
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
  intro ⟨hcons⟩
  constructor
  -- stateDependentDistanceError ≤ 2 * δ
  -- Reduce to pointwise: questionSDD ≤ 2 * questionConsistency
  unfold stateDependentDistanceError consistencyError at *
  calc averageOverDistribution 𝒟
        (fun q => questionStateDependentDistanceDefect ψ
          ((IndexedMeasurement.toIndexedSubMeasurement A) q)
          ((IndexedMeasurement.toIndexedSubMeasurement B) q))
      ≤ averageOverDistribution 𝒟
          (fun q => 2 * questionConsistencyDefect ψ
            ((IndexedMeasurement.toIndexedSubMeasurement A) q)
            ((IndexedMeasurement.toIndexedSubMeasurement B) q)) := by
        apply averageOverDistribution_mono
        intro q
        exact questionSDD_le_two_questionConsistency ψ (A q) (B q)
    _ = 2 * averageOverDistribution 𝒟
          (fun q => questionConsistencyDefect ψ
            ((IndexedMeasurement.toIndexedSubMeasurement A) q)
            ((IndexedMeasurement.toIndexedSubMeasurement B) q)) := by
        rw [averageOverDistribution_const_mul]
    _ ≤ 2 * δ := by
        exact mul_le_mul_of_nonneg_left hcons (by norm_num)

/-- Atomic mathematical fact: post-processing can only decrease the consistency
defect. Since `postprocess` preserves `totalOperator`, the coarse mismatch
terms are identical. For the fine matching-mass branch, merging outcomes
increases the matching mass `∑_b E[(Σ_{a:f(a)=b} A_a)(Σ_{a':f(a')=b} B_{a'})]
≥ ∑_a E[A_a B_a]`, so `totalOverlap - matchingMass` decreases. The cross-term
positivity `E[A_a B_{a'}] ≥ 0` requires PSD assumptions on the operators
and the state. -/
private lemma questionConsistencyDefect_postprocess_le {α β : Type*}
    (ψ : QuantumState) (A B : SubMeasurement α) (f : α → β) :
    questionConsistencyDefect ψ (postprocess A f) (postprocess B f) ≤
      questionConsistencyDefect ψ A B := by
  sorry

/-- `prop:simeq-data-processing`. -/
theorem simeqDataProcessing {Question α β : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question α) (δ : Error) (f : α → β) :
    consistency ψ 𝒟 A B δ →
      consistency ψ 𝒟
        (postprocessIndexedSubMeasurement A f)
        (postprocessIndexedSubMeasurement B f) δ := by
  intro ⟨hcons⟩
  constructor
  unfold consistencyError postprocessIndexedSubMeasurement postProcessing at *
  calc averageOverDistribution 𝒟
        (fun q => questionConsistencyDefect ψ (postprocess (A q) f) (postprocess (B q) f))
      ≤ averageOverDistribution 𝒟
          (fun q => questionConsistencyDefect ψ (A q) (B q)) := by
        apply averageOverDistribution_mono
        intro q
        exact questionConsistencyDefect_postprocess_le ψ (A q) (B q) f
    _ ≤ δ := hcons

/-! ### Infrastructure: triangle inequality for `StateDependentDistanceRel`

The squared-norm triangle inequality `‖u+v‖² ≤ 2(‖u‖² + ‖v‖²)` lifts to a
triangle inequality for state-dependent distance: if `A ≈_δ₁ B` and
`B ≈_δ₂ C`, then `A ≈_{2(δ₁+δ₂)} C`. This requires operator algebra
infrastructure (matrix PSD inequalities) that the scaffold does not yet
provide. -/

/-- Atomic mathematical fact: the parallelogram-style inequality
`E[(X-Z)†(X-Z)] ≤ 2(E[(X-Y)†(X-Y)] + E[(Y-Z)†(Y-Z)])` for the
`questionStateDependentDistanceDefect`. Follows from
`(X-Z) = (X-Y) + (Y-Z)` and the operator AM-GM inequality
`U†V + V†U ≤ U†U + V†V` (equivalently `0 ≤ (U-V)†(U-V)`),
which requires PSD trace positivity `E[D†D] ≥ 0`. -/
private lemma questionSDD_triangle {Outcome : Type*}
    (ψ : QuantumState) (A B C : SubMeasurement Outcome)
    (hψ : ψ.IsPositive) :
    questionStateDependentDistanceDefect ψ A C ≤
      2 * (questionStateDependentDistanceDefect ψ A B +
           questionStateDependentDistanceDefect ψ B C) := by
  sorry

/-- Triangle inequality for state-dependent distance. Requires PSD state for
the parallelogram inequality `E[D†D] ≥ 0`. -/
private lemma stateDependentDistanceRel_triangle
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B C : IndexedSubMeasurement Question Outcome) (δ₁ δ₂ : Error)
    (hψ : ψ.IsPositive) :
    StateDependentDistanceRel ψ 𝒟 A B δ₁ →
    StateDependentDistanceRel ψ 𝒟 B C δ₂ →
    StateDependentDistanceRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) := by
  intro ⟨h₁⟩ ⟨h₂⟩
  constructor
  unfold stateDependentDistanceError at *
  calc averageOverDistribution 𝒟
        (fun q => questionStateDependentDistanceDefect ψ (A q) (C q))
      ≤ averageOverDistribution 𝒟
          (fun q => 2 * (questionStateDependentDistanceDefect ψ (A q) (B q) +
                         questionStateDependentDistanceDefect ψ (B q) (C q))) := by
        apply averageOverDistribution_mono
        intro q
        exact questionSDD_triangle ψ (A q) (B q) (C q) hψ
    _ = 2 * averageOverDistribution 𝒟
          (fun q => questionStateDependentDistanceDefect ψ (A q) (B q) +
                     questionStateDependentDistanceDefect ψ (B q) (C q)) := by
        rw [averageOverDistribution_const_mul]
    _ = 2 * (averageOverDistribution 𝒟
              (fun q => questionStateDependentDistanceDefect ψ (A q) (B q)) +
             averageOverDistribution 𝒟
              (fun q => questionStateDependentDistanceDefect ψ (B q) (C q))) := by
        rw [averageOverDistribution_add]
    _ ≤ 2 * (δ₁ + δ₂) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add h₁ h₂

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

/-- Atomic fact: `∑_a E[(A_a - A_a B_a A_a)†(A_a - A_a B_a A_a)] ≤ γ`
when `A ≈_γ B` in consistency. The expansion uses `A_a - A_a B_a A_a =
A_a(I - B_a)A_a` which for projective `A_a` simplifies to `A_a(I - B_a)A_a`.
The sum over outcomes then telescopes to the off-diagonal mass.
Requires the tensor-product API (`leftTensor`/`rightTensor`) to handle
the bipartite placement. -/
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

/-- Atomic fact: `∑_a E[(A_a B_a A_a - A_a(Σ B)A_a)†(...)] ≤ γ`
when `A ≈_γ B` in consistency. The difference `A_a B_a A_a - A_a(Σ B)A_a
= -A_a(Σ_{b≠a} B_b)A_a`, and the sum telescopes to the off-diagonal mass.
Requires the tensor-product API for bipartite placement. -/
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
    (B : IndexedMeasurement Question Outcome) (γ : Error)
    (hψ : ψ.IsPositive) :
    StateDependentDistanceRel ψ 𝒟 A
      (diagonalSandwichFamily A B) γ →
    StateDependentDistanceRel ψ 𝒟
      (diagonalSandwichFamily A B)
      (totalSandwichFamily A B) γ →
    StateDependentDistanceRel ψ 𝒟 A
      (totalSandwichFamily A B) (4 * γ) := by
  intro hAD hDT
  have h := stateDependentDistanceRel_triangle ψ 𝒟 A
    (diagonalSandwichFamily A B) (totalSandwichFamily A B) γ γ hψ hAD hDT
  exact stateDependentDistanceRel_mono ψ 𝒟 A (totalSandwichFamily A B)
    (2 * (γ + γ)) (4 * γ) (by linarith) h

/-- `prop:cons-sub-meas`. Requires PSD state for the triangle inequality
used in `combinedControl`.
-- TODO: derive hψ from QuantumState once IsPositive is bundled into the type. -/
theorem consSubMeas {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) (γ : Error)
    (hψ : ψ.IsPositive) :
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
      consSubMeas_combinedControl ψ 𝒟 A B γ hψ hdc hsc
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
so the left and middle sandwich expectations are equal.
TODO(tensor): when `leftTensor` becomes a real tensor product, this equality
will need Cauchy-Schwarz; the proof should then become a sorry-backed bridge lemma. -/
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
so the middle and right sandwich expectations are equal.
TODO(tensor): when `rightTensor` becomes a real tensor product, this equality
will need projectivity; the proof should then become a sorry-backed bridge lemma. -/
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
trivial because `leftTensor` is a name-only operation.
TODO(tensor): will need Cauchy-Schwarz with real tensor API. -/
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
this is trivial because `rightTensor` is a name-only operation.
TODO(tensor): will need projectivity + Cauchy-Schwarz with real tensor API. -/
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

/-- Atomic fact: Cauchy-Schwarz at the operator level gives
`|E[A†P] - E[P†P]| ≤ √E[(A-P)†(A-P)] · √E[P†P]`. Combined with
`√(xy) ≤ (x+y)/2`, this yields `mass(A) ≥ mass(P) - 2√ε`. Requires
PSD trace positivity and the Cauchy-Schwarz inequality for the
normalized trace inner product. -/
private lemma completenessTransfer_core {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (P : IndexedProjectiveSubMeasurement Question Outcome) (ε : Error) :
    stateDependentDistanceError ψ 𝒟 A
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement P) ≤ ε →
    indexedSubMeasurementMass ψ 𝒟 A ≥
      indexedSubMeasurementMass ψ 𝒟
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement P)
        - 2 * Real.sqrt ε := by
  sorry

/-- `prop:completeness-transfer-projective-P`. -/
theorem completenessTransferProjectiveP {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (P : IndexedProjectiveSubMeasurement Question Outcome) (ε : Error) :
    stateDependentDistance ψ 𝒟 A
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement P) ε →
      CompletenessTransferProjectivePStatement ψ 𝒟 A P ε := by
  intro ⟨hε⟩
  exact { completenessTransfer := completenessTransfer_core ψ 𝒟 A P ε hε }

/-- The self-distance defect `questionStateDependentDistanceDefect ψ M M` is zero
because `operatorDifference X X` has zero matrix. Uses public
`operatorDifference_self_matrix` and `expectationValue_adjoint_mul_self_zero`
from `Basic/Operator.lean`. -/
private lemma questionStateDependentDistanceDefect_self
    {Outcome : Type*} (ψ : QuantumState) (M : SubMeasurement Outcome) :
    questionStateDependentDistanceDefect ψ M M = 0 := by
  unfold questionStateDependentDistanceDefect
  simp only
  have hfb : expectationValue ψ
      (operatorMul (operatorAdjoint (operatorDifference M.totalOperator M.totalOperator))
        (operatorDifference M.totalOperator M.totalOperator)) = 0 :=
    expectationValue_adjoint_mul_self_zero ψ _
      (operatorDifference_self_matrix M.totalOperator)
  have hpo : ∀ a, (fun a => expectationValue ψ
      (operatorMul (operatorAdjoint (operatorDifference (M.outcomeOperator a) (M.outcomeOperator a)))
        (operatorDifference (M.outcomeOperator a) (M.outcomeOperator a)))) a = 0 :=
    fun a => expectationValue_adjoint_mul_self_zero ψ _
      (operatorDifference_self_matrix (M.outcomeOperator a))
  unfold sumOverOutcomesOrElse
  split
  · simp [hpo]
  · exact hfb

/-- The self-distance `stateDependentDistanceError ψ 𝒟 A A` is zero at the
scaffold level because `operatorDifference X X` has zero matrix. Uses public
`MIPStarRE.LDT.averageOverDistribution_zero` from `Basic/Distribution.lean`. -/
private lemma stateDependentDistanceError_self {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) :
    stateDependentDistanceError ψ 𝒟 A A = 0 := by
  unfold stateDependentDistanceError
  have : (fun q => questionStateDependentDistanceDefect ψ (A q) (A q)) = fun _ => 0 :=
    funext (fun q => questionStateDependentDistanceDefect_self ψ (A q))
  rw [this]
  exact averageOverDistribution_zero 𝒟

/-- `strongSelfConsistencyError` is nonneg since it averages `max 0 (...)` terms
with nonneg weights. -/
private lemma strongSelfConsistencyError_nonneg {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) :
    0 ≤ strongSelfConsistencyError ψ 𝒟 A := by
  unfold strongSelfConsistencyError
  unfold averageOverDistribution
  apply List.sum_nonneg
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, _, rfl⟩ := hx
  apply mul_nonneg (𝒟.nonnegative a)
  unfold questionStrongSelfConsistencyDefect
  exact le_max_left 0 _

/-- `prop:two-notions-of-self-consistency`. At the scaffold level the self-distance
`stateDependentDistanceError ψ 𝒟 A A` is zero because `operatorDifference X X`
has zero matrix, so the bound `≤ 2 * δ` holds whenever `δ ≥ 0`.
When the tensor-product API becomes honest, this will need the expansion
`‖(A_a ⊗ I - I ⊗ A_a)|ψ⟩‖²` and comparison with the diagonal overlap. -/
theorem twoNotionsOfSelfConsistency {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) (δ : Error) :
    strongSelfConsistency ψ 𝒟 A δ →
      bipartiteStateDependentDistance ψ 𝒟 A A (2 * δ) := by
  intro ⟨_, ⟨hδ⟩⟩
  constructor
  rw [stateDependentDistanceError_self]
  have hδ_nonneg : 0 ≤ δ :=
    le_trans (strongSelfConsistencyError_nonneg ψ 𝒟 A) hδ
  linarith

/-- The closeness bound `2δ + 4√δ + 2ζ` for completing-to-measurement combines:
(1) `hdist`: A ≈_δ B in state-dependent distance,
(2) `hsc`: strong self-consistency of A with defect ζ,
(3) Triangle inequality: A ≈_{2δ} C via completion,
(4) Sandwich transfer: adds 4√δ from consSubMeas + switchSandwich,
(5) Self-consistency contributes 2ζ from twoNotionsOfSelfConsistency.
Requires the full consSubMeas, switchSandwich, and triangle machinery. -/
private lemma closenessAfterCompletion_core {Outcome : Type*}
    (ψ : QuantumState)
    (A : Measurement Outcome) (B : SubMeasurement Outcome)
    (a0 : Outcome) (δ ζ : Error) :
    strongSelfConsistency ψ (uniformDistribution Unit)
        (constantSubMeasurementFamily A.toSubMeasurement) ζ →
    stateDependentDistance ψ (uniformDistribution Unit)
        (constantSubMeasurementFamily A.toSubMeasurement)
        (constantSubMeasurementFamily B) δ →
    StateDependentDistanceRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily A.toSubMeasurement)
      (constantSubMeasurementFamily (completeAtOutcome B a0).toSubMeasurement)
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ) := by
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
  intro hsc hdist
  exact ⟨completeAtOutcome B a0, {
    completionFormula := rfl
    closenessAfterCompletion :=
      closenessAfterCompletion_core ψ A B a0 δ ζ hsc hdist
  }⟩

end MIPStarRE.LDT.Preliminaries
