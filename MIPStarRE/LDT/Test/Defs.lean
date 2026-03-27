import MIPStarRE.LDT.Basic.Parameters
import MIPStarRE.LDT.Basic.Operator
import MIPStarRE.LDT.Basic.Distribution
import MIPStarRE.LDT.Basic.SubMeasurement

/-!
# Section 3 — Definitions

Core definitions for the low individual degree test: evaluation families,
matching mass, consistency defect, and test-passing predicates.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.LDT

/-- Evaluate a polynomial-valued submeasurement at a point. -/
noncomputable def evaluateAt {d : ℕ} (params : Parameters) (u : Point params)
    (G : SubMeas (Polynomial params) d) : SubMeas (Fq params) d :=
  postprocess G (fun g => g u)

/-- View a global polynomial submeasurement as a point-indexed answer family. -/
noncomputable def polynomialEvaluationFamily {d : ℕ} (params : Parameters)
    (G : SubMeas (Polynomial params) d) :
    IdxSubMeas (Point params) (Fq params) d :=
  fun u => evaluateAt params u G

/-- Evaluate each member of an indexed polynomial family at the same point. -/
noncomputable def evaluateFiberFamilyAt {d : ℕ} (params : Parameters) (u : Point params)
    (G : IdxSubMeas (Fq params) (Polynomial params) d) :
    IdxSubMeas (Fq params) (Fq params) d :=
  fun x => evaluateAt params u (G x)

/-- Evaluate an indexed slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluateFiberFamilyAtNextPoint {d : ℕ} (params : Parameters)
    (G : IdxSubMeas (Fq params) (Polynomial params) d) :
    IdxSubMeas (Point params.next) (Fq params) d :=
  fun u => evaluateAt params (truncatePoint params u) (G (pointHeight params u))

/-- Questionwise matching mass `∑_a ⟨ψ, A_a B_a ψ⟩`, summed over outcomes. -/
noncomputable def qMatchMass {Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (A B : SubMeas Outcome d) : Error :=
  ∑ a, ev ψ (opMul (A.outcome a) (B.outcome a))

/-- Questionwise off-diagonal mass surrogate for consistency. -/
noncomputable def qConsDefect {Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (A B : SubMeas Outcome d) : Error :=
  let totalOverlap := ev ψ (opMul A.total B.total)
  max 0 (totalOverlap - qMatchMass ψ A B)

/-- Questionwise squared-distance defect. -/
noncomputable def qSDD {Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (A B : SubMeas Outcome d) : Error :=
  ∑ a, (let diff := opDiff (A.outcome a) (B.outcome a)
        ev ψ (opMul (opAdj diff) diff))

/-- Questionwise strong self-consistency defect. -/
noncomputable def qSSCDefect {Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (A : SubMeas Outcome d) : Error :=
  let totalMass := ev ψ A.total
  let diagonalMass := ∑ a, ev ψ (opMul (A.outcome a) (A.outcome a))
  max 0 (totalMass - diagonalMass)

/-- Averaged off-diagonal mass for consistency statements. -/
def consError {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome d) : Error :=
  avgOver 𝒟 (fun q => qConsDefect ψ (A q) (B q))

/-- Averaged squared distance for `≈_δ`. -/
def sddError {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome d) : Error :=
  avgOver 𝒟 (fun q => qSDD ψ (A q) (B q))

/-- Averaged defect in strong self-consistency. -/
def sscError {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d) : Error :=
  avgOver 𝒟 (fun q => qSSCDefect ψ (A q))

/-- Total mass of a submeasurement on state `ψ`, computed from the concrete total operator. -/
def subMeasMass {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A : SubMeas Outcome d) : Error :=
  ev ψ A.total

/-- Averaged total mass of an indexed submeasurement. -/
def idxSubMeasMass {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d) : Error :=
  avgOver 𝒟 (fun q => subMeasMass ψ (A q))

/-- Defect in domination by an operator witness, measured at the expectation-value level. -/
def bndError {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A : SubMeas Outcome d) (Z : Operator d) : Error :=
  max 0 (subMeasMass ψ A - ev ψ Z)

/-- Consistency relation. -/
structure ConsRel {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome d) (δ : Error) : Prop where
  offDiagonalBound : consError ψ 𝒟 A B ≤ δ

/-- State-dependent distance relation. -/
structure SDDRel {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome d) (δ : Error) : Prop where
  squaredDistanceBound : sddError ψ 𝒟 A B ≤ δ

/-- Strong self-consistency relation. -/
structure SSCRel {Question Outcome : Type*} {d : ℕ} [Fintype Outcome]
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome d) (δ : Error) : Prop where
  diagonalOverlapBound : sscError ψ 𝒟 A ≤ δ

/-- Completeness statement for a submeasurement. -/
structure CompletenessAtLeast {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A : SubMeas Outcome d) (r : Error) : Prop where
  lowerBound : subMeasMass ψ A ≥ r

/-- Boundedness statement witnessed by an operator. -/
structure BoundedByOperator {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A : SubMeas Outcome d) (Z : Operator d) (δ : Error) : Prop where
  witnessOpPSD : OpPSD Z
  upperBound : bndError ψ A Z ≤ δ

/-- Consistency between a points measurement and a global polynomial submeasurement. -/
structure ConsWithPolyEval {d : ℕ} (params : Parameters)
    (ψ : QuantumState d)
    (A : IdxSubMeas (Point params) (Fq params) d)
    (G : SubMeas (Polynomial params) d)
    (δ : Error) : Prop where
  evaluationConsistency :
    ConsRel ψ (uniformDistribution (Point params))
      A
      (polynomialEvaluationFamily params G)
      δ

/-- Consistency between two global polynomial submeasurements. -/
structure PolyMeasCons {d : ℕ} (params : Parameters)
    (ψ : QuantumState d)
    (G₁ G₂ : SubMeas (Polynomial params) d)
    (δ : Error) : Prop where
  mutualConsistency :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G₁)
      (constSubMeasFamily G₂)
      δ

/-- Strong self-consistency for a global polynomial submeasurement. -/
structure PolyMeasSSC {d : ℕ} (params : Parameters)
    (ψ : QuantumState d) (G : SubMeas (Polynomial params) d) (_δ : Error) : Prop where
  diagonalMassBound :
    SSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G)
      _δ

end MIPStarRE.LDT
