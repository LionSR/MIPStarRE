import MIPStarRE.LDT.Basic.Parameters
import MIPStarRE.LDT.Basic.Operator
import MIPStarRE.LDT.Basic.Distribution
import MIPStarRE.LDT.Basic.SubMeasurement

/-!
# Section 3 — Definitions

Core definitions for the low individual degree test: evaluation families,
matching mass, consistency defect, and test-passing predicates.

All operator fields now use `Op ι` directly with a generic `Fintype` index `ι`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.LDT

/-- Evaluate a polynomial-valued submeasurement at a point. -/
noncomputable def evaluateAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) (u : Point params)
    (G : SubMeas (Polynomial params) ι) : SubMeas (Fq params) ι :=
  postprocess G (fun g => g u)

/-- View a global polynomial submeasurement as a point-indexed answer family. -/
noncomputable def polynomialEvaluationFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (Point params) (Fq params) ι :=
  fun u => evaluateAt params u G

/-- Evaluate each member of an indexed polynomial family at the same point. -/
noncomputable def evaluateFiberFamilyAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) (u : Point params)
    (G : IdxSubMeas (Fq params) (Polynomial params) ι) :
    IdxSubMeas (Fq params) (Fq params) ι :=
  fun x => evaluateAt params u (G x)

/-- Evaluate an indexed slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluateFiberFamilyAtNextPoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters)
    (G : IdxSubMeas (Fq params) (Polynomial params) ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u => evaluateAt params (truncatePoint params u) (G (pointHeight params u))

/-- Questionwise matching mass `∑_a ⟨ψ, A_a B_a ψ⟩`, summed over outcomes. -/
noncomputable def qMatchMass {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) : Error :=
  ∑ a, ev ψ (A.outcome a * B.outcome a)

/-- Questionwise off-diagonal mass surrogate for consistency. -/
noncomputable def qConsDefect {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) : Error :=
  let totalOverlap := ev ψ (A.total * B.total)
  max 0 (totalOverlap - qMatchMass ψ A B)

/-- Questionwise squared-distance defect. -/
noncomputable def qSDD {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) : Error :=
  ∑ a, ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))

/-- Questionwise strong self-consistency defect. -/
noncomputable def qSSCDefect {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) : Error :=
  let totalMass := ev ψ A.total
  let diagonalMass := ∑ a, ev ψ (A.outcome a * A.outcome a)
  max 0 (totalMass - diagonalMass)

/-- Averaged off-diagonal mass for consistency statements. -/
def consError {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qConsDefect ψ (A q) (B q))

/-- Averaged squared distance for `≈_δ`. -/
def sddError {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qSDD ψ (A q) (B q))

/-- Averaged defect in strong self-consistency. -/
def sscError {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qSSCDefect ψ (A q))

/-- Total mass of a submeasurement on state `ψ`, computed from the concrete total operator. -/
def subMeasMass {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) : Error :=
  ev ψ A.total

/-- Averaged total mass of an indexed submeasurement. -/
def idxSubMeasMass {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => subMeasMass ψ (A q))

/-- Defect in domination by an operator witness, measured at the expectation-value level. -/
def bndError {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι)
    (Z : MIPStarRE.Quantum.Op ι) : Error :=
  max 0 (subMeasMass ψ A - ev ψ Z)

/-- Consistency relation. -/
structure ConsRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  offDiagonalBound : consError ψ 𝒟 A B ≤ δ

/-- State-dependent distance relation. -/
structure SDDRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  squaredDistanceBound : sddError ψ 𝒟 A B ≤ δ

/-- Strong self-consistency relation. -/
structure SSCRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  diagonalOverlapBound : sscError ψ 𝒟 A ≤ δ

/-- Completeness statement for a submeasurement. -/
structure CompletenessAtLeast {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) (r : Error) : Prop where
  lowerBound : subMeasMass ψ A ≥ r

/-- Boundedness statement witnessed by an operator. -/
structure BoundedByOperator {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι)
    (Z : MIPStarRE.Quantum.Op ι) (δ : Error) : Prop where
  witnessOpPSD : 0 ≤ Z
  upperBound : bndError ψ A Z ≤ δ

/-- Consistency between a points measurement and a global polynomial submeasurement. -/
structure ConsWithPolyEval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters)
    (ψ : QuantumState ι)
    (A : IdxSubMeas (Point params) (Fq params) ι)
    (G : SubMeas (Polynomial params) ι)
    (δ : Error) : Prop where
  evaluationConsistency :
    ConsRel ψ (uniformDistribution (Point params))
      A
      (polynomialEvaluationFamily params G)
      δ

/-- Consistency between two global polynomial submeasurements. -/
structure PolyMeasCons {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters)
    (ψ : QuantumState ι)
    (G₁ G₂ : SubMeas (Polynomial params) ι)
    (δ : Error) : Prop where
  mutualConsistency :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G₁)
      (constSubMeasFamily G₂)
      δ

/-- Strong self-consistency for a global polynomial submeasurement. -/
structure PolyMeasSSC {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters)
    (ψ : QuantumState ι) (G : SubMeas (Polynomial params) ι) (_δ : Error) : Prop where
  diagonalMassBound :
    SSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G)
      _δ

/-! ### Nonnegativity lemmas for defect measures -/

/-- The squared-distance defect is nonneg since each summand is `⟨ψ, M†M ψ⟩ ≥ 0`. -/
theorem qSDD_nonneg {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    0 ≤ qSDD ψ A B := by
  unfold qSDD
  exact Finset.sum_nonneg fun a _ => ev_adjoint_self_nonneg ψ _

/-- The consistency defect is nonneg by definition (`max 0 _`). -/
theorem qConsDefect_nonneg {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    0 ≤ qConsDefect ψ A B := by
  unfold qConsDefect; exact le_max_left 0 _

/-- The strong self-consistency defect is nonneg by definition (`max 0 _`). -/
theorem qSSCDefect_nonneg {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) :
    0 ≤ qSSCDefect ψ A := by
  unfold qSSCDefect; exact le_max_left 0 _

/-- The averaged squared-distance error is nonneg. -/
theorem sddError_nonneg {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) :
    0 ≤ sddError ψ 𝒟 A B := by
  unfold sddError; exact avgOver_nonneg 𝒟 _ fun q => qSDD_nonneg ψ _ _

/-- The averaged consistency error is nonneg. -/
theorem consError_nonneg {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) :
    0 ≤ consError ψ 𝒟 A B := by
  unfold consError; exact avgOver_nonneg 𝒟 _ fun q => qConsDefect_nonneg ψ _ _

/-- The averaged self-consistency error is nonneg. -/
theorem sscError_nonneg {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) :
    0 ≤ sscError ψ 𝒟 A := by
  unfold sscError; exact avgOver_nonneg 𝒟 _ fun q => qSSCDefect_nonneg ψ _

/-- The domination defect is nonneg by definition (`max 0 _`). -/
theorem bndError_nonneg {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) (Z : MIPStarRE.Quantum.Op ι) :
    0 ≤ bndError ψ A Z := by
  unfold bndError; exact le_max_left 0 _

/-! ### Postprocessing preserves totals -/

/-- Postprocessing preserves the total operator. -/
theorem postprocess_total {α β : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α]
    (A : SubMeas α ι) (f : α → β) :
    (postprocess A f).total = A.total := by
  simp [postprocess]

/-- The self-distance `qSDD ψ A A` is zero. -/
theorem qSDD_self {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) :
    qSDD ψ A A = 0 := by
  unfold qSDD
  apply Finset.sum_eq_zero
  intro a _
  simp [ev]

/-- The averaged self-distance `sddError ψ 𝒟 A A` is zero. -/
theorem sddError_self {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) :
    sddError ψ 𝒟 A A = 0 := by
  unfold sddError
  have : (fun q => qSDD ψ (A q) (A q)) = fun _ => 0 :=
    funext fun q => qSDD_self ψ (A q)
  rw [this]; exact avgOver_zero 𝒟

/-- Data processing: postprocessing can only decrease the consistency defect. -/
theorem qConsDefect_postprocess_le {α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (ψ : QuantumState ι) (A B : SubMeas α ι) (f : α → β) :
    qConsDefect ψ (postprocess A f) (postprocess B f) ≤
      qConsDefect ψ A B := by
  unfold qConsDefect
  simp only [postprocess_total]
  -- Suffices to show: matching mass increases under postprocessing
  -- i.e., ∑_b ⟨ψ, (∑_{a:f(a)=b} A_a)(∑_{c:f(c)=b} B_c) ψ⟩ ≥ ∑_a ⟨ψ, A_a B_a ψ⟩
  -- Then max(0, overlap - match') ≤ max(0, overlap - match) since match' ≥ match
  apply max_le_max_left 0
  apply sub_le_sub_left
  -- Need: qMatchMass after postprocessing ≥ qMatchMass before
  sorry

end MIPStarRE.LDT
