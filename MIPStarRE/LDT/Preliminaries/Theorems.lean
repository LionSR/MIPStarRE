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
theorem simeqForMeasurements {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome d) (δ : Error) :
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
private lemma questionSDD_le_two_questionConsistency {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A B : Measurement Outcome d) :
    questionStateDependentDistanceDefect ψ A.toSubMeasurement B.toSubMeasurement ≤
      2 * questionConsistencyDefect ψ A.toSubMeasurement B.toSubMeasurement := by
  sorry

/-- `prop:simeq-to-approx`. -/
theorem simeqToApprox {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome d) (δ : Error) :
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
private lemma questionConsistencyDefect_postprocess_le {α β : Type*} {d : ℕ}
    (ψ : QuantumState d) (A B : SubMeasurement α d) (f : α → β) :
    questionConsistencyDefect ψ (postprocess A f) (postprocess B f) ≤
      questionConsistencyDefect ψ A B := by
  sorry

/-- `prop:simeq-data-processing`. -/
theorem simeqDataProcessing {Question α β : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question α d) (δ : Error) (f : α → β) :
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
`B ≈_δ₂ C`, then `A ≈_{2(δ₁+δ₂)} C`. With the parametric dimension design,
no dimension hypotheses are needed. -/

/-- Atomic mathematical fact: the parallelogram-style inequality
`E[(X-Z)†(X-Z)] ≤ 2(E[(X-Y)†(X-Y)] + E[(Y-Z)†(Y-Z)])` for the
`questionStateDependentDistanceDefect`. Follows from
`(X-Z) = (X-Y) + (Y-Z)` and the operator AM-GM inequality
`U†V + V†U ≤ U†U + V†V` (equivalently `0 ≤ (U-V)†(U-V)`),
which requires PSD trace positivity `E[D†D] ≥ 0`. -/
private lemma questionSDD_triangle {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A B C : SubMeasurement Outcome d)
    (hψ : ψ.IsPositive) :
    questionStateDependentDistanceDefect ψ A C ≤
      2 * (questionStateDependentDistanceDefect ψ A B +
           questionStateDependentDistanceDefect ψ B C) := by
  -- Define shorthand for the per-outcome E[D†D] computation
  let ev (X Y : Operator d) := expectationValue ψ
    (operatorMul (operatorAdjoint (operatorDifference X Y)) (operatorDifference X Y))
  -- Pointwise triangle inequality from expectationValue_diff_triangle
  have pointwise_outcome : ∀ a, ev (A.outcomeOperator a) (C.outcomeOperator a) ≤
      2 * (ev (A.outcomeOperator a) (B.outcomeOperator a) +
           ev (B.outcomeOperator a) (C.outcomeOperator a)) :=
    fun a => expectationValue_diff_triangle ψ _ _ _ hψ
  have total_ineq : ev A.totalOperator C.totalOperator ≤
      2 * (ev A.totalOperator B.totalOperator + ev B.totalOperator C.totalOperator) :=
    expectationValue_diff_triangle ψ _ _ _ hψ
  -- Unfold the definition and handle both branches of sumOverOutcomesOrElse
  unfold questionStateDependentDistanceDefect
  simp only []
  -- The three sumOverOutcomesOrElse calls all branch on the same Nonempty (Fintype Outcome)
  unfold sumOverOutcomesOrElse
  split_ifs with hfin
  · -- Fintype case: use Finset.sum_le_sum + linearity
    letI : Fintype Outcome := Classical.choice hfin
    have h1 : ∑ a : Outcome, ev (A.outcomeOperator a) (C.outcomeOperator a) ≤
        ∑ a : Outcome, (2 * (ev (A.outcomeOperator a) (B.outcomeOperator a) +
                   ev (B.outcomeOperator a) (C.outcomeOperator a))) :=
      Finset.sum_le_sum (fun a _ => pointwise_outcome a)
    have h2 : ∑ a : Outcome, (2 * (ev (A.outcomeOperator a) (B.outcomeOperator a) +
                          ev (B.outcomeOperator a) (C.outcomeOperator a))) =
        2 * (∑ a : Outcome, ev (A.outcomeOperator a) (B.outcomeOperator a) +
             ∑ a : Outcome, ev (B.outcomeOperator a) (C.outcomeOperator a)) := by
      rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
    linarith
  · -- Fallback case
    exact total_ineq

/-- Triangle inequality for state-dependent distance. Requires PSD state for
the parallelogram inequality `E[D†D] ≥ 0`. -/
private lemma stateDependentDistanceRel_triangle
    {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B C : IndexedSubMeasurement Question Outcome d) (δ₁ δ₂ : Error)
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
    {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome d) (δ δ' : Error)
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
when `A ≈_γ B` in consistency. -/
private lemma consSubMeas_diagonalControl
    {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d)
    (B : IndexedMeasurement Question Outcome d) (γ : Error) :
    consistency ψ 𝒟 A
      (IndexedMeasurement.toIndexedSubMeasurement B) γ →
    StateDependentDistanceRel ψ 𝒟 A
      (diagonalSandwichFamily A B) γ := by
  sorry

/-- Atomic fact: `∑_a E[(A_a B_a A_a - A_a(Σ B)A_a)†(...)] ≤ γ`
when `A ≈_γ B` in consistency. -/
private lemma consSubMeas_sandwichControl
    {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d)
    (B : IndexedMeasurement Question Outcome d) (γ : Error) :
    consistency ψ 𝒟 A
      (IndexedMeasurement.toIndexedSubMeasurement B) γ →
    StateDependentDistanceRel ψ 𝒟
      (diagonalSandwichFamily A B)
      (totalSandwichFamily A B) γ := by
  sorry

/-- Combined bound from the triangle inequality for `≈_δ`:
`dist(A, totalSandwich) ≤ 4γ`. -/
private lemma consSubMeas_combinedControl
    {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d)
    (B : IndexedMeasurement Question Outcome d) (γ : Error)
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
    (diagonalSandwichFamily A B) (totalSandwichFamily A B) γ γ hψ
    hAD hDT
  exact stateDependentDistanceRel_mono ψ 𝒟 A (totalSandwichFamily A B)
    (2 * (γ + γ)) (4 * γ) (by linarith) h

/-- `prop:cons-sub-meas`. Requires PSD state for the triangle inequality
used in `combinedControl`.
-- TODO: derive hψ from QuantumState once IsPositive is bundled into the type. -/
theorem consSubMeas {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d)
    (B : IndexedMeasurement Question Outcome d) (γ : Error)
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

/-! ### Bridge lemmas for `prop:switch-sandwich` -/

/-- `expectationValue` depends only on the matrix, not on `name`. -/
private lemma expectationValue_name_irrel' {d : ℕ} (ψ : QuantumState d)
    (n₁ n₂ : String) (m : MIPStarRE.Quantum.Op (HilbertIndex d)) :
    expectationValue ψ ⟨n₁, m⟩ = expectationValue ψ ⟨n₂, m⟩ := rfl

/-- At scaffold level, `leftTensor` only changes the `name` field of an operator,
so the left and middle sandwich expectations are equal. -/
private lemma leftSandwich_eq_middleSandwich
    {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome d)
    (B : Operator d) :
    leftSandwichExpectation ψ 𝒟 A B = middleSandwichExpectation ψ 𝒟 A B := by
  unfold leftSandwichExpectation middleSandwichExpectation leftTensor operatorSandwich
  congr 1

/-- At scaffold level, `rightTensor` only changes the `name` field of an operator,
so the middle and right sandwich expectations are equal. -/
private lemma middleSandwich_eq_rightSandwich
    {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome d)
    (B : Operator d) :
    middleSandwichExpectation ψ 𝒟 A B = rightSandwichExpectation ψ 𝒟 A B := by
  unfold middleSandwichExpectation rightSandwichExpectation rightTensor operatorSandwich
  congr 1

/-- Left sandwich transfer bound. At scaffold level this is
trivial because `leftTensor` is a name-only operation. -/
private lemma switchSandwich_leftTransfer
    {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome d)
    (B : Operator d) (hB : OperatorBetweenZeroAndOne B)
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

/-- Right sandwich transfer bound. At scaffold level
this is trivial because `rightTensor` is a name-only operation. -/
private lemma switchSandwich_rightTransfer
    {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome d)
    (B : Operator d) (hB : OperatorBetweenZeroAndOne B)
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
theorem switchSandwich {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome d)
    (B : Operator d) (hB : OperatorBetweenZeroAndOne B)
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

/-- Atomic fact: Cauchy-Schwarz at the operator level. -/
private lemma completenessTransfer_core {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d)
    (P : IndexedProjectiveSubMeasurement Question Outcome d) (ε : Error) :
    stateDependentDistanceError ψ 𝒟 A
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement P) ≤ ε →
    indexedSubMeasurementMass ψ 𝒟 A ≥
      indexedSubMeasurementMass ψ 𝒟
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement P)
        - 2 * Real.sqrt ε := by
  sorry

/-- `prop:completeness-transfer-projective-P`. -/
theorem completenessTransferProjectiveP {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d)
    (P : IndexedProjectiveSubMeasurement Question Outcome d) (ε : Error) :
    stateDependentDistance ψ 𝒟 A
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement P) ε →
      CompletenessTransferProjectivePStatement ψ 𝒟 A P ε := by
  intro ⟨hε⟩
  exact { completenessTransfer := completenessTransfer_core ψ 𝒟 A P ε hε }

/-- The self-distance defect `questionStateDependentDistanceDefect ψ M M` is zero
because `operatorDifference X X` has zero matrix. -/
private lemma questionStateDependentDistanceDefect_self
    {Outcome : Type*} {d : ℕ} (ψ : QuantumState d) (M : SubMeasurement Outcome d) :
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

/-- The self-distance `stateDependentDistanceError ψ 𝒟 A A` is zero. -/
private lemma stateDependentDistanceError_self {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d) :
    stateDependentDistanceError ψ 𝒟 A A = 0 := by
  unfold stateDependentDistanceError
  have : (fun q => questionStateDependentDistanceDefect ψ (A q) (A q)) = fun _ => 0 :=
    funext (fun q => questionStateDependentDistanceDefect_self ψ (A q))
  rw [this]
  exact averageOverDistribution_zero 𝒟

/-- `strongSelfConsistencyError` is nonneg since it averages `max 0 (...)` terms
with nonneg weights. -/
private lemma strongSelfConsistencyError_nonneg {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d) :
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

/-- `prop:two-notions-of-self-consistency`. -/
theorem twoNotionsOfSelfConsistency {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d) (δ : Error) :
    strongSelfConsistency ψ 𝒟 A δ →
      bipartiteStateDependentDistance ψ 𝒟 A A (2 * δ) := by
  intro ⟨_, ⟨hδ⟩⟩
  constructor
  rw [stateDependentDistanceError_self]
  have hδ_nonneg : 0 ≤ δ :=
    le_trans (strongSelfConsistencyError_nonneg ψ 𝒟 A) hδ
  linarith

/-- Closeness bound `2δ + 4√δ + 2ζ` for completing-to-measurement. -/
private lemma closenessAfterCompletion_core {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d)
    (A : Measurement Outcome d) (B : SubMeasurement Outcome d)
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

/-- `prop:completing-to-measurement`. -/
theorem completingToMeasurement {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d)
    (A : Measurement Outcome d) (B : SubMeasurement Outcome d)
    (a0 : Outcome) (δ ζ : Error) :
    strongSelfConsistency ψ (uniformDistribution Unit)
        (constantSubMeasurementFamily A.toSubMeasurement) ζ →
      stateDependentDistance ψ (uniformDistribution Unit)
        (constantSubMeasurementFamily A.toSubMeasurement)
        (constantSubMeasurementFamily B) δ →
      ∃ C : Measurement Outcome d,
        CompletingToMeasurementStatement ψ A B C a0 δ ζ := by
  intro hsc hdist
  exact ⟨completeAtOutcome B a0, {
    completionFormula := rfl
    closenessAfterCompletion :=
      closenessAfterCompletion_core ψ A B a0 δ ζ hsc hdist
  }⟩

end MIPStarRE.LDT.Preliminaries
