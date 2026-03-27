import MIPStarRE.LDT.Preliminaries.Defs

/-!
Matching scaffold for Section 4 of the low individual degree paper in
`references/ldt-paper/preliminaries.tex`.

This file records the main proposition names with placeholder proofs.
All operator fields use `Op ι` directly.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:simeq-for-measurements`. -/
theorem simeqForMeasurements {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome ι) (δ : Error) :
    ConsRel ψ 𝒟 (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B) δ ↔
      ConsAgreement ψ 𝒟 A B δ := by
  constructor
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability; linarith⟩
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability at h; linarith⟩

/-- Atomic mathematical fact: for a full measurement, the squared-distance defect
is at most `2 * qConsDefect`. -/
private lemma questionSDD_le_two_questionConsistency {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : Measurement Outcome ι) :
    qSDD ψ A.toSubMeas B.toSubMeas ≤
      2 * qConsDefect ψ A.toSubMeas B.toSubMeas := by
  sorry

/-- `prop:simeq-to-approx`. -/
theorem simeqToApprox {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome ι) (δ : Error) :
    ConsRel ψ 𝒟 (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B) δ →
      BipartiteSDDRel ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B)
        (2 * δ) := by
  intro ⟨hcons⟩
  constructor
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
defect. -/
private lemma qConsDefect_postprocess_le {α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (ψ : QuantumState ι) (A B : SubMeas α ι) (f : α → β) :
    qConsDefect ψ (postprocess A f) (postprocess B f) ≤
      qConsDefect ψ A B := by
  sorry

/-- `prop:simeq-data-processing`. -/
theorem simeqDataProcessing {Question α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question α ι) (δ : Error) (f : α → β) :
    ConsRel ψ 𝒟 A B δ →
      ConsRel ψ 𝒟
        (fun q => postprocess (A q) f)
        (fun q => postprocess (B q) f) δ := by
  intro ⟨hcons⟩
  constructor
  unfold consError at *
  calc avgOver 𝒟
        (fun q => qConsDefect ψ (postprocess (A q) f) (postprocess (B q) f))
      ≤ avgOver 𝒟
          (fun q => qConsDefect ψ (A q) (B q)) := by
        apply avgOver_mono
        intro q
        exact qConsDefect_postprocess_le ψ (A q) (B q) f
    _ ≤ δ := hcons

/-! ### Infrastructure: triangle inequality for `SDDRel` -/

/-- Atomic mathematical fact: the parallelogram-style inequality for `qSDD`. -/
private lemma questionSDD_triangle {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B C : SubMeas Outcome ι) :
    qSDD ψ A C ≤
      2 * (qSDD ψ A B +
           qSDD ψ B C) := by
  let ev' (X Y : MIPStarRE.Quantum.Op ι) := ev ψ ((X - Y)ᴴ * (X - Y))
  have pointwise_outcome : ∀ a, ev' (A.outcome a) (C.outcome a) ≤
      2 * (ev' (A.outcome a) (B.outcome a) +
           ev' (B.outcome a) (C.outcome a)) :=
    fun a => ev_diff_triangle ψ _ _ _
  unfold qSDD
  have h1 : ∑ a : Outcome, ev' (A.outcome a) (C.outcome a) ≤
      ∑ a : Outcome, (2 * (ev' (A.outcome a) (B.outcome a) +
                 ev' (B.outcome a) (C.outcome a))) :=
    Finset.sum_le_sum (fun a _ => pointwise_outcome a)
  have h2 : ∑ a : Outcome, (2 * (ev' (A.outcome a) (B.outcome a) +
                        ev' (B.outcome a) (C.outcome a))) =
      2 * (∑ a : Outcome, ev' (A.outcome a) (B.outcome a) +
           ∑ a : Outcome, ev' (B.outcome a) (C.outcome a)) := by
    rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
  linarith

/-- Triangle inequality for state-dependent distance. -/
private lemma stateDependentDistanceRel_triangle
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxSubMeas Question Outcome ι) (δ₁ δ₂ : Error) :
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

/-- Monotonicity: if `SDDRel` holds for `δ`, it holds for any `δ' ≥ δ`. -/
private lemma stateDependentDistanceRel_mono
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ δ' : Error)
    (hle : δ ≤ δ') :
    SDDRel ψ 𝒟 A B δ →
    SDDRel ψ 𝒟 A B δ' := by
  intro ⟨h⟩
  exact ⟨le_trans h hle⟩

/-! ### Bridge lemmas for `prop:cons-sub-meas` -/

private lemma consSubMeas_diagonalControl
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
    ConsRel ψ 𝒟 A
      (IdxMeas.toIdxSubMeas B) γ →
    SDDRel ψ 𝒟 A
      (diagonalSandwichFamily A B) γ := by
  sorry

private lemma consSubMeas_sandwichControl
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
    ConsRel ψ 𝒟 A
      (IdxMeas.toIdxSubMeas B) γ →
    SDDRel ψ 𝒟
      (diagonalSandwichFamily A B)
      (totalSandwichFamily A B) γ := by
  sorry

private lemma consSubMeas_combinedControl
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
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

/-- `prop:cons-sub-meas`. -/
theorem consSubMeas {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
    ConsRel ψ 𝒟 A
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

/-! ### Bridge lemmas for `prop:switch-sandwich` -/

private lemma switchSandwich_leftTransfer
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (Alifted : IdxSubMeas Question Outcome (ι × ι))
    (B : MIPStarRE.Quantum.Op ι) (_hB : OpBounded01 B)
    (δ : Error) :
    BipartiteSDDRel ψ 𝒟 Alifted Alifted δ →
    |leftSandwichExpectation ψ 𝒟 A B -
      middleSandwichExpectation ψ 𝒟 A (leftTensor (ι₂ := ι) B)| ≤
      2 * Real.sqrt δ := by
  sorry

private lemma switchSandwich_rightTransfer
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (Alifted : IdxSubMeas Question Outcome (ι × ι))
    (B : MIPStarRE.Quantum.Op ι) (_hB : OpBounded01 B)
    (δ : Error) :
    BipartiteSDDRel ψ 𝒟 Alifted Alifted δ →
    |middleSandwichExpectation ψ 𝒟 A (rightTensor (ι₁ := ι) B) -
      rightSandwichExpectation ψ 𝒟 A B| ≤
      Real.sqrt δ := by
  sorry

/-- `prop:switch-sandwich`. -/
theorem switchSandwich {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (Alifted : IdxSubMeas Question Outcome (ι × ι))
    (B : MIPStarRE.Quantum.Op ι) (hB : OpBounded01 B)
    (δ : Error) :
    BipartiteSDDRel ψ 𝒟 Alifted Alifted δ →
    SwitchSandwichStmt ψ 𝒟 A B δ := by
  intro happrox
  exact {
    leftSandwichTransfer :=
      switchSandwich_leftTransfer ψ 𝒟 A Alifted B hB δ happrox
    rightSandwichTransfer :=
      switchSandwich_rightTransfer ψ 𝒟 A Alifted B hB δ happrox
  }

private lemma completenessTransfer_core {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (P : IdxProjSubMeas Question Outcome ι) (ε : Error) :
    sddError ψ 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ≤ ε →
    idxSubMeasMass ψ 𝒟 A ≥
      idxSubMeasMass ψ 𝒟
        (IdxProjSubMeas.toIdxSubMeas P)
        - 2 * Real.sqrt ε := by
  sorry

/-- `prop:completeness-transfer-projective-P`. -/
theorem completenessTransferProjectiveP {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (P : IdxProjSubMeas Question Outcome ι) (ε : Error) :
    SDDRel ψ 𝒟 A
        (IdxProjSubMeas.toIdxSubMeas P) ε →
      CompTransferStmt ψ 𝒟 A P ε := by
  intro ⟨hε⟩
  exact { completenessTransfer := completenessTransfer_core ψ 𝒟 A P ε hε }

/-- The self-distance defect `qSDD ψ M M` is zero. -/
private lemma qSDD_self
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (M : SubMeas Outcome ι) :
    qSDD ψ M M = 0 := by
  unfold qSDD
  apply Finset.sum_eq_zero
  intro a _
  simp [ev]

/-- The self-distance `sddError ψ 𝒟 A A` is zero. -/
private lemma sddError_self {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) :
    sddError ψ 𝒟 A A = 0 := by
  unfold sddError
  have : (fun q => qSDD ψ (A q) (A q)) = fun _ => 0 :=
    funext (fun q => qSDD_self ψ (A q))
  rw [this]
  exact avgOver_zero 𝒟

/-- `sscError` is nonneg since it averages `max 0 (...)` terms. -/
private lemma sscError_nonneg {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) :
    0 ≤ sscError ψ 𝒟 A := by
  unfold sscError
  exact avgOver_nonneg 𝒟 _ fun a => by unfold qSSCDefect; exact le_max_left 0 _

/-- `prop:two-notions-of-self-consistency`. -/
theorem twoNotionsOfSelfConsistency {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    (PermInvState ψ ∧ SSCRel ψ 𝒟 A δ) →
      BipartiteSDDRel ψ 𝒟 A A (2 * δ) := by
  intro ⟨_, ⟨hδ⟩⟩
  constructor
  rw [sddError_self]
  have hδ_nonneg : 0 ≤ δ :=
    le_trans (sscError_nonneg ψ 𝒟 A) hδ
  linarith

private lemma closenessAfterCompletion_core {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (B : SubMeas Outcome ι)
    (a0 : Outcome) (δ ζ : Error) :
    (PermInvState ψ ∧ SSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ) →
    SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B) δ →
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily (completeAtOutcome B a0).toSubMeas)
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ) := by
  sorry

/-- `prop:completing-to-measurement`. -/
theorem completingToMeasurement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (B : SubMeas Outcome ι)
    (a0 : Outcome) (δ ζ : Error) :
    (PermInvState ψ ∧ SSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas) ζ) →
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily B) δ →
      ∃ C : Measurement Outcome ι,
        CompletingToMeasStmt ψ A B C a0 δ ζ := by
  intro hsc hdist
  exact ⟨completeAtOutcome B a0, {
    completionFormula := rfl
    closenessAfterCompletion :=
      closenessAfterCompletion_core ψ A B a0 δ ζ hsc hdist
  }⟩

end MIPStarRE.LDT.Preliminaries
