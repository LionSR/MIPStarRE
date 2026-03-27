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
    (G : SubMeasurement (Polynomial params) d) : SubMeasurement (Fq params) d :=
  postprocess G (fun g => g u)

/-- View a global polynomial submeasurement as a point-indexed answer family. -/
noncomputable def polynomialEvaluationFamily {d : ℕ} (params : Parameters)
    (G : SubMeasurement (Polynomial params) d) :
    IndexedSubMeasurement (Point params) (Fq params) d :=
  fun u => evaluateAt params u G

/-- Evaluate each member of an indexed polynomial family at the same point. -/
noncomputable def evaluateFiberFamilyAt {d : ℕ} (params : Parameters) (u : Point params)
    (G : IndexedSubMeasurement (Fq params) (Polynomial params) d) :
    IndexedSubMeasurement (Fq params) (Fq params) d :=
  fun x => evaluateAt params u (G x)

/-- Evaluate an indexed slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluateFiberFamilyAtNextPoint {d : ℕ} (params : Parameters)
    (G : IndexedSubMeasurement (Fq params) (Polynomial params) d) :
    IndexedSubMeasurement (Point params.next) (Fq params) d :=
  fun u => evaluateAt params (truncatePoint params u) (G (pointHeight params u))

/-- Questionwise matching mass `∑_a ⟨ψ, A_a B_a ψ⟩`, summed over outcomes when the
outcome space is enumerable. -/
noncomputable def questionMatchingMass {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A B : SubMeasurement Outcome d) : Error :=
  sumOverOutcomesOrElse
    (expectationValue ψ (operatorMul A.totalOperator B.totalOperator))
    (fun a => expectationValue ψ (operatorMul (A.outcomeOperator a) (B.outcomeOperator a)))

/-- Questionwise off-diagonal mass surrogate for consistency. -/
noncomputable def questionConsistencyDefect {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A B : SubMeasurement Outcome d) : Error := by
  classical
  let totalOverlap := expectationValue ψ (operatorMul A.totalOperator B.totalOperator)
  let coarseMismatch :=
    max 0
      (expectationValue ψ A.totalOperator + expectationValue ψ B.totalOperator - 2 * totalOverlap)
  if h : Nonempty (Fintype Outcome) then
    exact max 0 (totalOverlap - questionMatchingMass ψ A B)
  else
    exact coarseMismatch

/-- Questionwise squared-distance defect. -/
noncomputable def questionStateDependentDistanceDefect {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A B : SubMeasurement Outcome d) : Error :=
  let totalDiff := operatorDifference A.totalOperator B.totalOperator
  sumOverOutcomesOrElse
    (expectationValue ψ (operatorMul (operatorAdjoint totalDiff) totalDiff))
    (fun a =>
      let diff := operatorDifference (A.outcomeOperator a) (B.outcomeOperator a)
      expectationValue ψ (operatorMul (operatorAdjoint diff) diff))

/-- Questionwise strong self-consistency defect. -/
noncomputable def questionStrongSelfConsistencyDefect {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A : SubMeasurement Outcome d) : Error :=
  let totalMass := expectationValue ψ A.totalOperator
  let coarseDiagonal := expectationValue ψ (operatorMul A.totalOperator A.totalOperator)
  let diagonalMass :=
    sumOverOutcomesOrElse coarseDiagonal
      (fun a => expectationValue ψ (operatorMul (A.outcomeOperator a) (A.outcomeOperator a)))
  max 0 (totalMass - diagonalMass)

/-- Averaged off-diagonal mass for consistency statements. -/
def consistencyError {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome d) : Error :=
  averageOverDistribution 𝒟 (fun q => questionConsistencyDefect ψ (A q) (B q))

/-- Averaged squared distance for `≈_δ`. -/
def stateDependentDistanceError {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome d) : Error :=
  averageOverDistribution 𝒟 (fun q => questionStateDependentDistanceDefect ψ (A q) (B q))

/-- Averaged defect in strong self-consistency. -/
def strongSelfConsistencyError {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d) : Error :=
  averageOverDistribution 𝒟 (fun q => questionStrongSelfConsistencyDefect ψ (A q))

/-- Total mass of a submeasurement on state `ψ`, computed from the concrete total operator. -/
def subMeasurementMass {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A : SubMeasurement Outcome d) : Error :=
  expectationValue ψ A.totalOperator

/-- Averaged total mass of an indexed submeasurement. -/
def indexedSubMeasurementMass {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d) : Error :=
  averageOverDistribution 𝒟 (fun q => subMeasurementMass ψ (A q))

/-- Defect in domination by an operator witness, measured at the expectation-value level. -/
def boundednessError {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A : SubMeasurement Outcome d) (Z : Operator d) : Error :=
  max 0 (subMeasurementMass ψ A - expectationValue ψ Z)

/-- Consistency relation. -/
structure ConsistencyRel {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome d) (δ : Error) : Prop where
  offDiagonalBound : consistencyError ψ 𝒟 A B ≤ δ

/-- State-dependent distance relation. -/
structure StateDependentDistanceRel {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome d) (δ : Error) : Prop where
  squaredDistanceBound : stateDependentDistanceError ψ 𝒟 A B ≤ δ

/-- Strong self-consistency relation. -/
structure StrongSelfConsistencyRel {Question Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome d) (δ : Error) : Prop where
  diagonalOverlapBound : strongSelfConsistencyError ψ 𝒟 A ≤ δ

/-- Completeness statement for a submeasurement. -/
structure CompletenessAtLeast {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A : SubMeasurement Outcome d) (r : Error) : Prop where
  lowerBound : subMeasurementMass ψ A ≥ r

/-- Boundedness statement witnessed by an operator. -/
structure BoundedByOperator {Outcome : Type*} {d : ℕ}
    (ψ : QuantumState d) (A : SubMeasurement Outcome d) (Z : Operator d) (δ : Error) : Prop where
  witnessPositiveSemidefinite : PositiveSemidefinite Z
  upperBound : boundednessError ψ A Z ≤ δ

/-- Consistency between a points measurement and a global polynomial submeasurement. -/
structure ConsistentWithPolynomialEvaluation {d : ℕ} (params : Parameters)
    (ψ : QuantumState d)
    (A : IndexedSubMeasurement (Point params) (Fq params) d)
    (G : SubMeasurement (Polynomial params) d)
    (δ : Error) : Prop where
  evaluationConsistency :
    ConsistencyRel ψ (uniformDistribution (Point params))
      A
      (polynomialEvaluationFamily params G)
      δ

/-- Consistency between two global polynomial submeasurements. -/
structure PolynomialMeasurementsConsistent {d : ℕ} (params : Parameters)
    (ψ : QuantumState d)
    (G₁ G₂ : SubMeasurement (Polynomial params) d)
    (δ : Error) : Prop where
  mutualConsistency :
    ConsistencyRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily G₁)
      (constantSubMeasurementFamily G₂)
      δ

/-- Strong self-consistency for a global polynomial submeasurement. -/
structure PolynomialMeasurementStronglySelfConsistent {d : ℕ} (params : Parameters)
    (ψ : QuantumState d) (G : SubMeasurement (Polynomial params) d) (_δ : Error) : Prop where
  diagonalMassBound :
    StrongSelfConsistencyRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily G)
      _δ

end MIPStarRE.LDT
