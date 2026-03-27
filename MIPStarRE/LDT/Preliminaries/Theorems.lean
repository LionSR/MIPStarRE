import MIPStarRE.LDT.Preliminaries.Defs

/-!
Matching scaffold for Section 4 of the low individual degree paper in
`references/ldt-paper/preliminaries.tex`.

This file records the main proposition names with placeholder proofs.
-/

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:simeq-for-measurements`. The equivalence is definitional:
`agreementProbability = 1 - consError`, so `consError ≤ δ`
iff `agreementProbability ≥ 1 - δ`. -/
theorem simeqForMeasurements {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome d) (δ : Error) :
    consistency ψ 𝒟 (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B) δ ↔
      ConsAgreement ψ 𝒟 A B δ := by
  unfold consistency
  constructor
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability; linarith⟩
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability at h; linarith⟩

/-- Atomic mathematical fact: for a full measurement (`Σ A_a = I`),
the squared-distance defect `∑_a E[(A_a-B_a)†(A_a-B_a)]` is at most
`2 * qConsDefect`. This requires measurement completeness
(not yet enforced by the scaffold `Measurement` type) and the expansion
`‖A_a - B_a‖² = E[A_a²] + E[B_a²] - E[A_a B_a] - E[B_a A_a]`
combined with `Σ_a E[A_a²] ≤ Σ_a E[A_a] = 1`. -/
private lemma questionSDD_le_two_questionConsistency {Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (A B : Measurement Outcome d) :
    qSDD ψ A.toSubMeas B.toSubMeas ≤
      2 * qConsDefect ψ A.toSubMeas B.toSubMeas := by
  sorry

/-- `prop:simeq-to-approx`. -/
theorem simeqToApprox {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome d) (δ : Error) :
    consistency ψ 𝒟 (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B) δ →
      bipartiteStateDependentDistance ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B)
        (2 * δ) := by
  intro ⟨hcons⟩
  constructor
  -- sddError ≤ 2 * δ
  -- Reduce to pointwise: questionSDD ≤ 2 * questionConsistency
  unfold sddError consError at *
  calc avgOver 𝒟
        (fun q => qSDD ψ
          ((IdxMeas.toIdxSubMeas A) q)
          ((IdxMeas.toIdxSubMeas B) q))
      ≤ avgOver 𝒟
          (fun q => 2 * qConsDefect ψ
            ((IdxMeas.toIdxSubMeas A) q)
            ((IdxMeas.toIdxSubMeas B) q)) := by
        apply avgOver_mono
        intro q
        exact questionSDD_le_two_questionConsistency ψ (A q) (B q)
    _ = 2 * avgOver 𝒟
          (fun q => qConsDefect ψ
            ((IdxMeas.toIdxSubMeas A) q)
            ((IdxMeas.toIdxSubMeas B) q)) := by
        rw [avgOver_const_mul]
    _ ≤ 2 * δ := by
        exact mul_le_mul_of_nonneg_left hcons (by norm_num)

/-- Atomic mathematical fact: post-processing can only decrease the consistency
defect. Since `postprocess` preserves `totalOperator`, the coarse mismatch
terms are identical. For the fine matching-mass branch, merging outcomes
increases the matching mass `∑_b E[(Σ_{a:f(a)=b} A_a)(Σ_{a':f(a')=b} B_{a'})]
≥ ∑_a E[A_a B_a]`, so `totalOverlap - matchingMass` decreases. The cross-term
positivity `E[A_a B_{a'}] ≥ 0` requires PSD assumptions on the operators
and the state. -/
private lemma qConsDefect_postprocess_le {α β : Type*} {d : ℕ} [Fintype α] [Fintype β]
    (ψ : QuantumState d) (A B : SubMeas α d) (f : α → β) :
    qConsDefect ψ (postprocess A f) (postprocess B f) ≤
      qConsDefect ψ A B := by
  sorry

/-- `prop:simeq-data-processing`. -/
theorem simeqDataProcessing {Question α β : Type*} {d : ℕ} [Fintype α] [Fintype β]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question α d) (δ : Error) (f : α → β) :
    consistency ψ 𝒟 A B δ →
      consistency ψ 𝒟
        (postprocessIdxSubMeas A f)
        (postprocessIdxSubMeas B f) δ := by
  intro ⟨hcons⟩
  constructor
  unfold consError postprocessIdxSubMeas postProcessing at *
  calc avgOver 𝒟
        (fun q => qConsDefect ψ (postprocess (A q) f) (postprocess (B q) f))
      ≤ avgOver 𝒟
          (fun q => qConsDefect ψ (A q) (B q)) := by
        apply avgOver_mono
        intro q
        exact qConsDefect_postprocess_le ψ (A q) (B q) f
    _ ≤ δ := hcons

/-! ### Infrastructure: triangle inequality for `SDDRel`

The squared-norm triangle inequality `‖u+v‖² ≤ 2(‖u‖² + ‖v‖²)` lifts to a
triangle inequality for state-dependent distance: if `A ≈_δ₁ B` and
`B ≈_δ₂ C`, then `A ≈_{2(δ₁+δ₂)} C`. With the parametric dimension design,
no dimension hypotheses are needed. -/

/-- Atomic mathematical fact: the parallelogram-style inequality
`E[(X-Z)†(X-Z)] ≤ 2(E[(X-Y)†(X-Y)] + E[(Y-Z)†(Y-Z)])` for the
`qSDD`. Follows from
`(X-Z) = (X-Y) + (Y-Z)` and the operator AM-GM inequality
`U†V + V†U ≤ U†U + V†V` (equivalently `0 ≤ (U-V)†(U-V)`),
which requires PSD trace positivity `E[D†D] ≥ 0`. -/
private lemma questionSDD_triangle {Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (A B C : SubMeas Outcome d) :
    qSDD ψ A C ≤
      2 * (qSDD ψ A B +
           qSDD ψ B C) := by
  -- Define shorthand for the per-outcome E[D†D] computation
  let ev (X Y : Operator d) := ev ψ
    (opMul (opAdj (opDiff X Y)) (opDiff X Y))
  -- Pointwise triangle inequality from ev_diff_triangle
  have pointwise_outcome : ∀ a, ev (A.outcome a) (C.outcome a) ≤
      2 * (ev (A.outcome a) (B.outcome a) +
           ev (B.outcome a) (C.outcome a)) :=
    fun a => ev_diff_triangle ψ _ _ _
  -- Unfold the definition and use Finset.sum_le_sum + linearity
  unfold qSDD
  simp only []
  have h1 : ∑ a : Outcome, ev (A.outcome a) (C.outcome a) ≤
      ∑ a : Outcome, (2 * (ev (A.outcome a) (B.outcome a) +
                 ev (B.outcome a) (C.outcome a))) :=
    Finset.sum_le_sum (fun a _ => pointwise_outcome a)
  have h2 : ∑ a : Outcome, (2 * (ev (A.outcome a) (B.outcome a) +
                        ev (B.outcome a) (C.outcome a))) =
      2 * (∑ a : Outcome, ev (A.outcome a) (B.outcome a) +
           ∑ a : Outcome, ev (B.outcome a) (C.outcome a)) := by
    rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  linarith

/-- Triangle inequality for state-dependent distance. Requires PSD state for
the parallelogram inequality `E[D†D] ≥ 0`. -/
private lemma stateDependentDistanceRel_triangle
    {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B C : IdxSubMeas Question Outcome d) (δ₁ δ₂ : Error) :
    SDDRel ψ 𝒟 A B δ₁ →
    SDDRel ψ 𝒟 B C δ₂ →
    SDDRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) := by
  intro ⟨h₁⟩ ⟨h₂⟩
  constructor
  unfold sddError at *
  calc avgOver 𝒟
        (fun q => qSDD ψ (A q) (C q))
      ≤ avgOver 𝒟
          (fun q => 2 * (qSDD ψ (A q) (B q) +
                         qSDD ψ (B q) (C q))) := by
        apply avgOver_mono
        intro q
        exact questionSDD_triangle ψ (A q) (B q) (C q)
    _ = 2 * avgOver 𝒟
          (fun q => qSDD ψ (A q) (B q) +
                     qSDD ψ (B q) (C q)) := by
        rw [avgOver_const_mul]
    _ = 2 * (avgOver 𝒟
              (fun q => qSDD ψ (A q) (B q)) +
             avgOver 𝒟
              (fun q => qSDD ψ (B q) (C q))) := by
        rw [avgOver_add]
    _ ≤ 2 * (δ₁ + δ₂) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add h₁ h₂

/-- Monotonicity: if `SDDRel` holds for `δ`,
it holds for any `δ' ≥ δ`. -/
private lemma stateDependentDistanceRel_mono
    {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome d) (δ δ' : Error)
    (hle : δ ≤ δ') :
    SDDRel ψ 𝒟 A B δ →
    SDDRel ψ 𝒟 A B δ' := by
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
    {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d)
    (B : IdxMeas Question Outcome d) (γ : Error) :
    consistency ψ 𝒟 A
      (IdxMeas.toIdxSubMeas B) γ →
    SDDRel ψ 𝒟 A
      (diagonalSandwichFamily A B) γ := by
  sorry

/-- Atomic fact: `∑_a E[(A_a B_a A_a - A_a(Σ B)A_a)†(...)] ≤ γ`
when `A ≈_γ B` in consistency. -/
private lemma consSubMeas_sandwichControl
    {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d)
    (B : IdxMeas Question Outcome d) (γ : Error) :
    consistency ψ 𝒟 A
      (IdxMeas.toIdxSubMeas B) γ →
    SDDRel ψ 𝒟
      (diagonalSandwichFamily A B)
      (totalSandwichFamily A B) γ := by
  sorry

/-- Combined bound from the triangle inequality for `≈_δ`:
`dist(A, totalSandwich) ≤ 4γ`. -/
private lemma consSubMeas_combinedControl
    {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d)
    (B : IdxMeas Question Outcome d) (γ : Error) :
    SDDRel ψ 𝒟 A
      (diagonalSandwichFamily A B) γ →
    SDDRel ψ 𝒟
      (diagonalSandwichFamily A B)
      (totalSandwichFamily A B) γ →
    SDDRel ψ 𝒟 A
      (totalSandwichFamily A B) (4 * γ) := by
  intro hAD hDT
  have h := stateDependentDistanceRel_triangle ψ 𝒟 A
    (diagonalSandwichFamily A B) (totalSandwichFamily A B) γ γ
    hAD hDT
  exact stateDependentDistanceRel_mono ψ 𝒟 A (totalSandwichFamily A B)
    (2 * (γ + γ)) (4 * γ) (by linarith) h

/-- `prop:cons-sub-meas`. PSD state is bundled into `QuantumState`. -/
theorem consSubMeas {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d)
    (B : IdxMeas Question Outcome d) (γ : Error) :
    consistency ψ 𝒟 A
      (IdxMeas.toIdxSubMeas B) γ →
    ConsSubMeasStmt ψ 𝒟 A B γ := by
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

With the honest bipartite tensor-product model, `leftTensor` / `rightTensor`
change the underlying matrix (via Kronecker products), so the left/right
sandwich expectations are no longer trivially equal to the middle one.
The inequalities require `Matrix.mul_kronecker_mul` and related
Kronecker-product algebra, which is tracked as `TODO(kron)`. -/

/-- `ev` depends only on the matrix, not on `name`. -/
private lemma ev_name_irrel' {d : ℕ} (ψ : QuantumState d)
    (n₁ n₂ : String) (m : MIPStarRE.Quantum.Op (HilbertIndex d)) :
    ev ψ ⟨n₁, m⟩ = ev ψ ⟨n₂, m⟩ := rfl

/-- Left sandwich transfer bound.  Requires honest Kronecker-product
algebra (`Matrix.mul_kronecker_mul`) to relate `(A_q ⊗ I)(B ⊗ I)(A_q ⊗ I)`
to `(A_q B A_q) ⊗ I`.

The hypothesis `Alifted` is the bipartite-lifted version of the local
measurement family (each outcome tensored with identity on the second register).
-/
-- TODO(kron): needs Matrix.mul_kronecker_mul and Kronecker trace factorization
private lemma switchSandwich_leftTransfer
    {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState (d * d)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome d)
    (Alifted : IdxSubMeas Question Outcome (d * d))
    (B : Operator d) (_hB : OpBounded01 B)
    (δ : Error) :
    bipartiteStateDependentDistance ψ 𝒟 Alifted Alifted δ →
    |leftSandwichExpectation ψ 𝒟 A B -
      middleSandwichExpectation ψ 𝒟 A (leftTensor (d₂ := d) B)| ≤
      2 * Real.sqrt δ := by
  sorry

/-- Right sandwich transfer bound.  Requires honest Kronecker-product
algebra to relate `(A_q ⊗ I)(I ⊗ B)(A_q ⊗ I)` to `(A_q² ⊗ B)`. -/
-- TODO(kron): needs Matrix.mul_kronecker_mul and Kronecker trace factorization
private lemma switchSandwich_rightTransfer
    {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState (d * d)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome d)
    (Alifted : IdxSubMeas Question Outcome (d * d))
    (B : Operator d) (_hB : OpBounded01 B)
    (δ : Error) :
    bipartiteStateDependentDistance ψ 𝒟 Alifted Alifted δ →
    |middleSandwichExpectation ψ 𝒟 A (rightTensor (d₁ := d) B) -
      rightSandwichExpectation ψ 𝒟 A B| ≤
      Real.sqrt δ := by
  sorry

/-- `prop:switch-sandwich`.

The hypothesis uses `Alifted`, the bipartite-lifted version of `A`.
Callers should provide the result of lifting each `A_q` outcome via
`leftTensor`. -/
-- TODO(kron): proof needs real Kronecker algebra (was trivial when leftTensor was name-only)
theorem switchSandwich {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState (d * d)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome d)
    (Alifted : IdxSubMeas Question Outcome (d * d))
    (B : Operator d) (hB : OpBounded01 B)
    (δ : Error) :
    bipartiteStateDependentDistance ψ 𝒟 Alifted Alifted δ →
    SwitchSandwichStmt ψ 𝒟 A B δ := by
  intro happrox
  exact {
    leftSandwichTransfer :=
      switchSandwich_leftTransfer ψ 𝒟 A Alifted B hB δ happrox
    rightSandwichTransfer :=
      switchSandwich_rightTransfer ψ 𝒟 A Alifted B hB δ happrox
  }

/-- Atomic fact: Cauchy-Schwarz at the operator level. -/
private lemma completenessTransfer_core {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d)
    (P : IdxProjSubMeas Question Outcome d) (ε : Error) :
    sddError ψ 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ≤ ε →
    idxSubMeasMass ψ 𝒟 A ≥
      idxSubMeasMass ψ 𝒟
        (IdxProjSubMeas.toIdxSubMeas P)
        - 2 * Real.sqrt ε := by
  sorry

/-- `prop:completeness-transfer-projective-P`. -/
theorem completenessTransferProjectiveP {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d)
    (P : IdxProjSubMeas Question Outcome d) (ε : Error) :
    stateDependentDistance ψ 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ε →
      CompTransferStmt ψ 𝒟 A P ε := by
  intro ⟨hε⟩
  exact { completenessTransfer := completenessTransfer_core ψ 𝒟 A P ε hε }

/-- The self-distance defect `qSDD ψ M M` is zero
because `opDiff X X` has zero matrix. -/
private lemma qSDD_self
    {Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (M : SubMeas Outcome d) :
    qSDD ψ M M = 0 := by
  unfold qSDD
  simp only
  have hpo : ∀ a, (fun a => ev ψ
      (opMul (opAdj (opDiff (M.outcome a) (M.outcome a)))
        (opDiff (M.outcome a) (M.outcome a)))) a = 0 :=
    fun a => ev_adjoint_mul_self_zero ψ _
      (opDiff_self_matrix (M.outcome a))
  simp [hpo]

/-- The self-distance `sddError ψ 𝒟 A A` is zero. -/
private lemma sddError_self {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d) :
    sddError ψ 𝒟 A A = 0 := by
  unfold sddError
  have : (fun q => qSDD ψ (A q) (A q)) = fun _ => 0 :=
    funext (fun q => qSDD_self ψ (A q))
  rw [this]
  exact avgOver_zero 𝒟

/-- `sscError` is nonneg since it averages `max 0 (...)` terms
with nonneg weights. -/
private lemma sscError_nonneg {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d) :
    0 ≤ sscError ψ 𝒟 A := by
  unfold sscError
  unfold avgOver
  apply List.sum_nonneg
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, _, rfl⟩ := hx
  apply mul_nonneg (𝒟.nonnegative a)
  unfold qSSCDefect
  exact le_max_left 0 _

/-- `prop:two-notions-of-self-consistency`. -/
theorem twoNotionsOfSelfConsistency {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d) (δ : Error) :
    strongSelfConsistency ψ 𝒟 A δ →
      bipartiteStateDependentDistance ψ 𝒟 A A (2 * δ) := by
  intro ⟨_, ⟨hδ⟩⟩
  constructor
  rw [sddError_self]
  have hδ_nonneg : 0 ≤ δ :=
    le_trans (sscError_nonneg ψ 𝒟 A) hδ
  linarith

/-- Closeness bound `2δ + 4√δ + 2ζ` for completing-to-measurement. -/
private lemma closenessAfterCompletion_core {Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d)
    (A : Measurement Outcome d) (B : SubMeas Outcome d)
    (a0 : Outcome) (δ ζ : Error) :
    strongSelfConsistency ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ →
    stateDependentDistance ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B) δ →
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily (completeAtOutcome B a0).toSubMeas)
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ) := by
  sorry

/-- `prop:completing-to-measurement`. -/
theorem completingToMeasurement {Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d)
    (A : Measurement Outcome d) (B : SubMeas Outcome d)
    (a0 : Outcome) (δ ζ : Error) :
    strongSelfConsistency ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ →
      stateDependentDistance ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B) δ →
      ∃ C : Measurement Outcome d,
        CompletingToMeasStmt ψ A B C a0 δ ζ := by
  intro hsc hdist
  exact ⟨completeAtOutcome B a0, {
    completionFormula := rfl
    closenessAfterCompletion :=
      closenessAfterCompletion_core ψ A B a0 δ ζ hsc hdist
  }⟩

end MIPStarRE.LDT.Preliminaries
