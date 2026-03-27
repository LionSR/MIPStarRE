import MIPStarRE.LDT.Test.MainTheorem

/-!
Matching scaffold for Section 4 of the low individual degree paper in
`references/ldt-paper/preliminaries.tex`.

This file introduces lightweight paper-local definitions for the measurement
calculus of the paper.
-/

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `def:post-processing` in `preliminaries.tex`. -/
noncomputable def postProcessing {α β : Type*} {d : ℕ} [Fintype α]
    (A : SubMeas α d) (f : α → β) :
    SubMeas β d :=
  postprocess A f

/-- `def:measurement-completion` in `preliminaries.tex`. -/
def measurementCompletion {α : Type*} {d : ℕ} (A : SubMeas α d) :
    Measurement (Option α) d :=
  completeSubMeas A

/-- `def:simeq` in `preliminaries.tex`. -/
def consistency {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome d) (δ : Error) : Prop :=
  ConsRel ψ 𝒟 A B δ

/-- `def:approx_delta` in `preliminaries.tex`. -/
def stateDependentDistance {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome d) (δ : Error) : Prop :=
  SDDRel ψ 𝒟 A B δ

/-- `def:strong-self-consistency` in `preliminaries.tex`. -/
def strongSelfConsistency {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d) (δ : Error) : Prop :=
  PermInvState ψ ∧ SSCRel ψ 𝒟 A δ

/-- Source-style left/right relation `A^x_a ⊗ I ≈_δ I ⊗ B^x_a`.

TODO(tensor): this currently reuses the single-register comparison layer from Section 3,
so users should wrap `A` and `B` in the local `leftTensor` / `rightTensor` placements
before invoking it. Replacing this by an honest tensor-product API remains future work.
-/
structure BipartiteSDDRel {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome d) (δ : Error) : Prop where
  leftRightSquaredDistanceBound : sddError ψ 𝒟 A B ≤ δ

/-- Abbreviation for the bipartite state-dependent distance used in the source propositions. -/
def bipartiteStateDependentDistance {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome d) (δ : Error) : Prop :=
  BipartiteSDDRel ψ 𝒟 A B δ

/-- Condition `0 ≤ B ≤ I` for the switch-sandwich argument, with the identity taken in
`B`'s ambient dimension. -/
structure OpBounded01 {d : ℕ} (B : Operator d) : Prop where
  nonnegative : OpPSD B
  boundedByIdentity : OpDominates (identityLike B) B

/-- Placeholder agreement probability from `prop:simeq-for-measurements`. -/
noncomputable def agreementProbability {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome d) : Error :=
  1 - consError ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas B)

/-- Output package for the measurement reformulation of consistency. -/
structure ConsAgreement {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxMeas Question Outcome d) (δ : Error) : Prop where
  agreementLowerBound : agreementProbability ψ 𝒟 A B ≥ 1 - δ

/-- Post-process an indexed family questionwise. -/
noncomputable def postprocessIdxSubMeas {Question α β : Type*} {d : ℕ} [Fintype α]
    (A : IdxSubMeas Question α d) (f : α → β) :
    IdxSubMeas Question β d :=
  fun q => postProcessing (A q) f

/-- The completion residual `I - Σ_a B_a` used when completing a
submeasurement. -/
noncomputable def completionResidualOperator {Outcome : Type*} {d : ℕ}
    (B : SubMeas Outcome d) : Operator d :=
  opDiff (identityLike B.total) B.total

/-- Family for the intermediate `A_a B_a A_a` sandwich. -/
noncomputable def diagonalSandwichFamily {Question Outcome : Type*} {d : ℕ}
    (A : IdxSubMeas Question Outcome d)
    (B : IdxMeas Question Outcome d) :
    IdxSubMeas Question Outcome d :=
  fun q => {
    name := s!"{(A q).name}.diagSandwich({(B q).toSubMeas.name})"
    outcome := fun a =>
      opSandwich
        ((A q).outcome a)
        ((B q).toSubMeas.outcome a)
        ((A q).outcome a)
    total := (A q).total
  }

/-- Family for the intermediate `A_a (Σ_b B_b) A_a` sandwich. -/
noncomputable def totalSandwichFamily {Question Outcome : Type*} {d : ℕ}
    (A : IdxSubMeas Question Outcome d)
    (B : IdxMeas Question Outcome d) :
    IdxSubMeas Question Outcome d :=
  fun q => {
    name := s!"{(A q).name}.totalSandwich({(B q).toSubMeas.name})"
    outcome := fun a =>
      opSandwich
        ((A q).outcome a)
        (B q).toSubMeas.total
        ((A q).outcome a)
    total := (A q).total
  }

/-- Output package for `prop:cons-sub-meas`. -/
structure ConsSubMeasStmt {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d)
    (B : IdxMeas Question Outcome d) (γ : Error) : Prop where
  diagonalControl :
    SDDRel ψ 𝒟 A (diagonalSandwichFamily A B) γ
  sandwichControl :
    SDDRel ψ 𝒟 (diagonalSandwichFamily A B) (totalSandwichFamily A B) γ
  combinedControl :
    SDDRel ψ 𝒟 A (totalSandwichFamily A B) (4 * γ)

/-- Averaged left-placed sandwich scalar from `prop:switch-sandwich`.

In the bipartite model for symmetric strategies, `ψ` lives on `H ⊗ H`
(dimension `d * d`), `A` is a projective sub-measurement family on `H`,
and `B` is a bounded operator on `H`.  The left-placed sandwich puts
`B` on the *left* register: `E_q ⟨ψ| (A_q ⊗ I)(B ⊗ I)(A_q ⊗ I) |ψ⟩`. -/
noncomputable def leftSandwichExpectation {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState (d * d)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome d)
    (B : Operator d) : Error :=
  avgOver 𝒟 fun q =>
    ev ψ <|
      opSandwich
        (leftTensor (d₂ := d) (A q).toSubMeas.total)
        (leftTensor (d₂ := d) B)
        (leftTensor (d₂ := d) (A q).toSubMeas.total)

/-- Averaged middle sandwich scalar from `prop:switch-sandwich`.

In the middle sandwich, `B` is an operator already on the full bipartite
space `d * d`.  The measurement total is lifted:
`E_q ⟨ψ| (A_q ⊗ I) B (A_q ⊗ I) |ψ⟩`. -/
noncomputable def middleSandwichExpectation {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState (d * d)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome d)
    (B : Operator (d * d)) : Error :=
  avgOver 𝒟 fun q =>
    ev ψ <|
      opSandwich
        (leftTensor (d₂ := d) (A q).toSubMeas.total)
        B
        (leftTensor (d₂ := d) (A q).toSubMeas.total)

/-- Averaged right-placed sandwich scalar from `prop:switch-sandwich`.

In the bipartite model, the right-placed sandwich puts `B` on the
*right* register: `E_q ⟨ψ| (A_q ⊗ I)(I ⊗ B)(A_q ⊗ I) |ψ⟩`. -/
noncomputable def rightSandwichExpectation {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState (d * d)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome d)
    (B : Operator d) : Error :=
  avgOver 𝒟 fun q =>
    ev ψ <|
      opSandwich
        (leftTensor (d₂ := d) (A q).toSubMeas.total)
        (rightTensor (d₁ := d) B)
        (leftTensor (d₂ := d) (A q).toSubMeas.total)

/-- Output package for `prop:switch-sandwich`.

In the bipartite model, `B : Operator d` is a local operator on one register,
and we compare sandwiching by `B ⊗ I` (left) and `I ⊗ B` (right)
around `A_q ⊗ I`. -/
structure SwitchSandwichStmt {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState (d * d)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome d)
    (B : Operator d) (δ : Error) : Prop where
  leftSandwichTransfer :
    |leftSandwichExpectation ψ 𝒟 A B -
      middleSandwichExpectation ψ 𝒟 A (leftTensor (d₂ := d) B)|
      ≤ 2 * Real.sqrt δ
  rightSandwichTransfer :
    |middleSandwichExpectation ψ 𝒟 A (rightTensor (d₁ := d) B) -
      rightSandwichExpectation ψ 𝒟 A B|
      ≤ Real.sqrt δ

/-- Output package for `prop:completeness-transfer-projective-P`. -/
structure CompTransferStmt {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d)
    (P : IdxProjSubMeas Question Outcome d) (ε : Error) : Prop where
  completenessTransfer :
    idxSubMeasMass ψ 𝒟 A ≥
      idxSubMeasMass ψ 𝒟
        (IdxProjSubMeas.toIdxSubMeas P)
        - 2 * Real.sqrt ε

/-- Canonical completion of `B` by adjoining the residual `I - Σ_a B_a`
to the distinguished outcome `a0`. -/
noncomputable def completeAtOutcome {Outcome : Type*} {d : ℕ}
    (B : SubMeas Outcome d) (a0 : Outcome) : Measurement Outcome d := by
  classical
  let residual := completionResidualOperator B
  refine {
    toSubMeas := {
      name := s!"{B.name}.completed"
      outcome := fun a =>
        if h : a = a0 then
          opAdd (B.outcome a) residual
        else
          B.outcome a
      total := identityLike B.total
    }
  }

/-- Output package for `prop:completing-to-measurement`. -/
structure CompletingToMeasStmt {Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d)
    (A : Measurement Outcome d) (B : SubMeas Outcome d)
    (C : Measurement Outcome d) (a0 : Outcome) (δ ζ : Error) : Prop where
  completionFormula : C = completeAtOutcome B a0
  closenessAfterCompletion :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily C.toSubMeas)
      (2 * δ + 4 * Real.sqrt δ + 2 * ζ)

end MIPStarRE.LDT.Preliminaries
