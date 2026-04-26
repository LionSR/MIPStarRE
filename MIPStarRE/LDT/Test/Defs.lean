import MIPStarRE.LDT.Basic.ParametersFiniteAnswers
import MIPStarRE.LDT.Basic.OperatorExpectations
import MIPStarRE.LDT.Basic.Distribution
import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.Basic.OpFamily

/-!
# Section 3 — Definitions

Core definitions for the low individual degree test: evaluation families,
matching mass, consistency defect, and test-passing predicates.

All operator fields now use `Op ι` directly with a generic `Fintype` index `ι`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- Evaluate a polynomial-valued submeasurement at a point. -/
noncomputable def evaluateAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q] (u : Point params)
    (G : SubMeas (Polynomial params) ι) : SubMeas (Fq params) ι :=
  postprocess G (fun g => g u)

/-- View a global polynomial submeasurement as a point-indexed answer family. -/
noncomputable def polynomialEvaluationFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (Point params) (Fq params) ι :=
  fun u => evaluateAt params u G

/-- Evaluate each member of an indexed polynomial family at the same point. -/
noncomputable def evaluateFiberFamilyAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q] (u : Point params)
    (G : IdxSubMeas (Fq params) (Polynomial params) ι) :
    IdxSubMeas (Fq params) (Fq params) ι :=
  fun x => evaluateAt params u (G x)

/-- Evaluate an indexed slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluateFiberFamilyAtNextPoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
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
noncomputable def qSDDCore {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A B : Outcome → MIPStarRE.Quantum.Op ι) : Error :=
  ∑ a, ev ψ ((A a - B a)ᴴ * (A a - B a))

/-- Questionwise squared-distance defect. -/
noncomputable def qSDD {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) : Error :=
  qSDDCore ψ A.outcome B.outcome

/-- State-dependent distance for raw operator families.
Matches the paper's `≈_δ` for arbitrary matrix families.
This keeps the raw-family API separate while sharing the same core formula as
`qSDD`. -/
noncomputable def qSDDOp {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : OpFamily Outcome ι) : Error :=
  qSDDCore ψ A.outcome B.outcome

/-- Questionwise strong self-consistency defect. -/
noncomputable def qSSCDefect {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) : Error :=
  let totalMass := ev ψ A.total
  let diagonalMass := ∑ a, ev ψ (A.outcome a * A.outcome a)
  max 0 (totalMass - diagonalMass)

/-- Averaged off-diagonal mass for consistency statements. -/
noncomputable def consError {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qConsDefect ψ (A q) (B q))

/-- Averaged squared distance for `≈_δ`. -/
noncomputable def sddError {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qSDD ψ (A q) (B q))

/-- Averaged squared distance for raw operator families. -/
noncomputable def sddErrorOp {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qSDDOp ψ (A q) (B q))

/-- Averaged defect in strong self-consistency. -/
noncomputable def sscError {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qSSCDefect ψ (A q))

/-- Total mass of a submeasurement on state `ψ`, computed from the concrete total operator. -/
noncomputable def subMeasMass {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) : Error :=
  ev ψ A.total

/-- Averaged total mass of an indexed submeasurement. -/
noncomputable def idxSubMeasMass {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => subMeasMass ψ (A q))

/-- Defect in domination by an operator witness, measured at the expectation-value level. -/
noncomputable def bndError {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι)
    (Z : MIPStarRE.Quantum.Op ι) : Error :=
  max 0 (subMeasMass ψ A - ev ψ Z)

/-- Bipartite matching mass `∑_a ⟨ψ, (A_a ⊗ B_a) ψ⟩`, with `A` on the left
register and `B` on the right register of a tensor-product state. -/
noncomputable def qBipartiteMatchMass {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) : Error :=
  ∑ a, ev ψ (opTensor (A.outcome a) (B.outcome a))

/-- Bipartite questionwise consistency defect.

In the paper (Definition 4.8), the consistency of `A` on `H_A` and `B` on
`H_B` for a shared state `|ψ⟩ ∈ H_A ⊗ H_B` is:
  `E_x ∑_{a≠b} ⟨ψ| A^x_a ⊗ B^x_b |ψ⟩ ≤ δ`
which equals
  `max 0 (⟨ψ| A_total ⊗ B_total |ψ⟩ − ∑_a ⟨ψ| A_a ⊗ B_a |ψ⟩)`. -/
noncomputable def qBipartiteConsDefect {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) : Error :=
  let totalOverlap := ev ψ (opTensor A.total B.total)
  max 0 (totalOverlap - qBipartiteMatchMass ψ A B)

/-- Averaged bipartite off-diagonal mass for consistency statements. -/
noncomputable def bipartiteConsError {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ιA)
    (B : IdxSubMeas Question Outcome ιB) : Error :=
  avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q))

/-- **Bridge lemma**: the bipartite consistency defect equals the same-space
`qConsDefect` applied to the left/right-placed submeasurements. -/
theorem qBipartiteConsDefect_eq_qConsDefect_placed {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) :
    qBipartiteConsDefect ψ A B =
      qConsDefect ψ (leftPlacedSubMeas A) (rightPlacedSubMeas B) := by
  simp only [qBipartiteConsDefect, qConsDefect, qBipartiteMatchMass, qMatchMass,
    leftPlacedSubMeas_total, rightPlacedSubMeas_total,
    leftPlacedSubMeas_outcome, rightPlacedSubMeas_outcome,
    leftTensor_mul_rightTensor_eq_opTensor]

/-- **Bridge lemma**: averaged bipartite consistency equals the same-space
`consError` applied to the left/right-placed families. -/
theorem bipartiteConsError_eq_consError_placed {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ιA)
    (B : IdxSubMeas Question Outcome ιB) :
    bipartiteConsError ψ 𝒟 A B =
      consError ψ 𝒟
        (fun q => leftPlacedSubMeas (A q))
        (fun q => rightPlacedSubMeas (B q)) := by
  unfold bipartiteConsError consError
  congr 1; funext q
  exact qBipartiteConsDefect_eq_qConsDefect_placed ψ (A q) (B q)

/-- Consistency relation (bipartite, paper Definition 4.8).

The state `ψ` lives on `H_A ⊗ H_B`, Alice's submeasurement `A` acts on
`H_A`, and Bob's submeasurement `B` acts on `H_B`. The relation encodes
  `E_{x ∼ D} ∑_{a≠b} ⟨ψ| A^x_a ⊗ B^x_b |ψ⟩ ≤ δ`. -/
structure ConsRel {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ιA)
    (B : IdxSubMeas Question Outcome ιB)
    (δ : Error) : Prop where
  offDiagonalBound : bipartiteConsError ψ 𝒟 A B ≤ δ

/-- State-dependent distance relation. -/
structure SDDRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  squaredDistanceBound : sddError ψ 𝒟 A B ≤ δ

/-- State-dependent distance relation for raw operator families. -/
structure SDDOpRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) : Prop where
  squaredDistanceBound : sddErrorOp ψ 𝒟 A B ≤ δ

/-- Strong self-consistency relation. -/
structure SSCRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  diagonalOverlapBound : sscError ψ 𝒟 A ≤ δ

/-- Bipartite questionwise strong self-consistency defect.
This is the paper's SSC condition (Definition 4.3/4.4):
  `max 0 (∑ₐ ev ψ (Aₐ ⊗ I) − ∑ₐ ev ψ (Aₐ ⊗ Aₐ))`.
It measures the gap between the total mass on one register and the
diagonal cross-register overlap. -/
noncomputable def qBipartiteSSCDefect
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι) : Error :=
  let totalMass := ev ψ (leftTensor (ι₂ := ι) A.total)
  let overlapMass := ∑ a, ev ψ (opTensor (A.outcome a) (A.outcome a))
  max 0 (totalMass - overlapMass)

/-- Averaged bipartite SSC defect. -/
noncomputable def bipartiteSSCError
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q))

/-- Bipartite strong self-consistency relation (paper's definition).
Uses the cross-register overlap `∑ₐ ev ψ (Aₐ ⊗ Aₐ)` rather than
the local square `∑ₐ ev ψ (Aₐ² ⊗ I)`. -/
structure BipartiteSSCRel
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  overlapBound : bipartiteSSCError ψ 𝒟 A ≤ δ

/-- Completeness statement for a submeasurement. -/
structure CompletenessAtLeast {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) (r : Error) : Prop where
  lowerBound : subMeasMass ψ A ≥ r

/-- Boundedness statement witnessed by an operator. -/
structure BoundedByOperator {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι)
    (Z : MIPStarRE.Quantum.Op ι) (δ : Error) : Prop where
  witnessOpPSD : 0 ≤ Z
  upperBound : bndError ψ A Z ≤ δ

/-! ### Nonnegativity lemmas for defect measures -/

/-- The squared-distance defect is nonneg since each summand is `⟨ψ, M†M ψ⟩ ≥ 0`. -/
theorem qSDD_nonneg {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    0 ≤ qSDD ψ A B := by
  unfold qSDD qSDDCore
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

/-- The bipartite consistency defect is nonneg by definition (`max 0 _`). -/
theorem qBipartiteConsDefect_nonneg {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) :
    0 ≤ qBipartiteConsDefect ψ A B := by
  unfold qBipartiteConsDefect; exact le_max_left 0 _

/-- The averaged bipartite consistency error is nonneg. -/
theorem bipartiteConsError_nonneg {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ιA)
    (B : IdxSubMeas Question Outcome ιB) :
    0 ≤ bipartiteConsError ψ 𝒟 A B := by
  unfold bipartiteConsError
  exact avgOver_nonneg 𝒟 _ fun q => qBipartiteConsDefect_nonneg ψ _ _

/-- The bipartite matching mass is nonnegative because each summand is the
expectation of a positive semidefinite tensor product. -/
theorem qBipartiteMatchMass_nonneg {Outcome : Type*}
    {ιA ιB : Type*} [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) :
    0 ≤ qBipartiteMatchMass ψ A B := by
  unfold qBipartiteMatchMass
  exact Finset.sum_nonneg fun a _ =>
    ev_nonneg_of_psd ψ _ (opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a))

/-- For a normalized state, a bipartite consistency defect is at most `1`. -/
theorem qBipartiteConsDefect_le_one_of_isNormalized {Outcome : Type*}
    {ιA ιB : Type*} [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) :
    qBipartiteConsDefect ψ A B ≤ 1 := by
  have hmatch_nonneg : 0 ≤ qBipartiteMatchMass ψ A B :=
    qBipartiteMatchMass_nonneg ψ A B
  have htotal_le_one : ev ψ (opTensor A.total B.total) ≤ 1 := by
    calc
      ev ψ (opTensor A.total B.total)
        ≤ ev ψ (leftTensor (ι₂ := ιB) A.total) := by
            exact ev_mono ψ _ _
              (opTensor_le_leftTensor (ι₂ := ιB) (SubMeas.total_nonneg A) B.total_le_one)
      _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
            exact ev_mono ψ _ _ (leftTensor_le_one (ι₂ := ιB) A.total_le_one)
      _ = 1 := ev_one_of_isNormalized ψ hψ
  unfold qBipartiteConsDefect
  apply max_le
  · norm_num
  · linarith

/-- Under a probability question distribution, the averaged bipartite consistency
error is bounded by `1`. -/
theorem bipartiteConsError_le_one_of_isProbability {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question) (h𝒟 : 𝒟.IsProbability)
    (A : IdxSubMeas Question Outcome ιA) (B : IdxSubMeas Question Outcome ιB) :
    bipartiteConsError ψ 𝒟 A B ≤ 1 := by
  unfold bipartiteConsError
  calc
    avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q))
      ≤ avgOver 𝒟 (fun _ : Question => 1) := by
          refine avgOver_mono _ _ _ ?_
          intro q
          exact qBipartiteConsDefect_le_one_of_isNormalized ψ hψ (A q) (B q)
    _ = 1 := avgOver_const_of_isProbability 𝒟 h𝒟 1

/-- Under a bundled probability question distribution, the averaged bipartite
consistency error is bounded by `1`. -/
theorem bipartiteConsError_le_one_of_probabilityDistribution {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : ProbabilityDistribution Question)
    (hψ : ψ.IsNormalized)
    (A : IdxSubMeas Question Outcome ιA) (B : IdxSubMeas Question Outcome ιB) :
    bipartiteConsError ψ (𝒟 : Distribution Question) A B ≤ 1 := by
  exact bipartiteConsError_le_one_of_isProbability ψ hψ (𝒟 : Distribution Question) 𝒟.2 A B

/-- Under the uniform question distribution, the averaged bipartite consistency
error is bounded by `1`. -/
theorem bipartiteConsError_uniform_le_one {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome] [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : IdxSubMeas Question Outcome ιA) (B : IdxSubMeas Question Outcome ιB) :
    bipartiteConsError ψ (uniformDistribution Question) A B ≤ 1 := by
  simpa [uniformProbabilityDistribution] using
    bipartiteConsError_le_one_of_probabilityDistribution ψ
      (uniformProbabilityDistribution Question) hψ A B

/-- The bipartite strong self-consistency defect is nonneg by definition (`max 0 _`). -/
theorem qBipartiteSSCDefect_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι) :
    0 ≤ qBipartiteSSCDefect ψ A := by
  unfold qBipartiteSSCDefect
  exact le_max_left 0 _

/-- The averaged bipartite strong self-consistency error is nonneg. -/
theorem bipartiteSSCError_nonneg {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) :
    0 ≤ bipartiteSSCError ψ 𝒟 A := by
  unfold bipartiteSSCError
  exact avgOver_nonneg 𝒟 _ fun q => qBipartiteSSCDefect_nonneg ψ _

/-- The averaged self-consistency error is nonneg. -/
theorem sscError_nonneg {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) :
    0 ≤ sscError ψ 𝒟 A := by
  unfold sscError; exact avgOver_nonneg 𝒟 _ fun q => qSSCDefect_nonneg ψ _

/-- The domination defect is nonneg by definition (`max 0 _`). -/
theorem bndError_nonneg {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) (Z : MIPStarRE.Quantum.Op ι) :
    0 ≤ bndError ψ A Z := by
  unfold bndError; exact le_max_left 0 _

/-! ### Postprocessing preserves totals -/

/-- Postprocessing preserves the total operator. -/
theorem postprocess_total {α β : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (f : α → β) :
    (postprocess A f).total = A.total := by
  rfl

/-- The self-distance `qSDD ψ A A` is zero. -/
theorem qSDD_self {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) :
    qSDD ψ A A = 0 := by
  unfold qSDD qSDDCore
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

/- The naive monotonicity statement
`qConsDefect ψ (postprocess A f) (postprocess B f) ≤ qConsDefect ψ A B`
is false for arbitrary submeasurements: without opposite-side / commuting
hypotheses, the extra cross terms created by postprocessing need not be
nonnegative. The paper's data-processing proposition is therefore recorded in
the bipartite form `Preliminaries.simeqDataProcessing`, not as a generic fact
about `qConsDefect`. -/

end MIPStarRE.LDT
