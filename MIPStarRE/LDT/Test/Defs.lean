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
noncomputable def evaluateAt (params : Parameters) (u : Point params)
    (G : SubMeasurement (Polynomial params)) : SubMeasurement (Fq params) :=
  postprocess G (fun g => g u)

/-- View a global polynomial submeasurement as a point-indexed answer family. -/
noncomputable def polynomialEvaluationFamily (params : Parameters)
    (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (Point params) (Fq params) :=
  fun u => evaluateAt params u G

/-- Evaluate each member of an indexed polynomial family at the same point. -/
noncomputable def evaluateFiberFamilyAt (params : Parameters) (u : Point params)
    (G : IndexedSubMeasurement (Fq params) (Polynomial params)) :
    IndexedSubMeasurement (Fq params) (Fq params) :=
  fun x => evaluateAt params u (G x)

/-- Evaluate an indexed slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluateFiberFamilyAtNextPoint (params : Parameters)
    (G : IndexedSubMeasurement (Fq params) (Polynomial params)) :
    IndexedSubMeasurement (Point params.next) (Fq params) :=
  fun u => evaluateAt params (truncatePoint params u) (G (pointHeight params u))

/-- Questionwise matching mass `∑_a ⟨ψ, A_a B_a ψ⟩`, summed over outcomes when the
outcome space is enumerable. -/
noncomputable def questionMatchingMass {Outcome : Type*}
    (ψ : QuantumState) (A B : SubMeasurement Outcome) : Error :=
  sumOverOutcomesOrElse
    (expectationValue ψ (operatorMul A.totalOperator B.totalOperator))
    (fun a => expectationValue ψ (operatorMul (A.outcomeOperator a) (B.outcomeOperator a)))

/-- Questionwise off-diagonal mass surrogate for consistency. -/
noncomputable def questionConsistencyDefect {Outcome : Type*}
    (ψ : QuantumState) (A B : SubMeasurement Outcome) : Error := by
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
noncomputable def questionStateDependentDistanceDefect {Outcome : Type*}
    (ψ : QuantumState) (A B : SubMeasurement Outcome) : Error :=
  let totalDiff := operatorDifference A.totalOperator B.totalOperator
  sumOverOutcomesOrElse
    (expectationValue ψ (operatorMul (operatorAdjoint totalDiff) totalDiff))
    (fun a =>
      let diff := operatorDifference (A.outcomeOperator a) (B.outcomeOperator a)
      expectationValue ψ (operatorMul (operatorAdjoint diff) diff))

/-- Questionwise strong self-consistency defect. -/
noncomputable def questionStrongSelfConsistencyDefect {Outcome : Type*}
    (ψ : QuantumState) (A : SubMeasurement Outcome) : Error :=
  let totalMass := expectationValue ψ A.totalOperator
  let coarseDiagonal := expectationValue ψ (operatorMul A.totalOperator A.totalOperator)
  let diagonalMass :=
    sumOverOutcomesOrElse coarseDiagonal
      (fun a => expectationValue ψ (operatorMul (A.outcomeOperator a) (A.outcomeOperator a)))
  max 0 (totalMass - diagonalMass)

/-- Averaged off-diagonal mass for consistency statements. -/
def consistencyError {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) : Error :=
  averageOverDistribution 𝒟 (fun q => questionConsistencyDefect ψ (A q) (B q))

/-- Averaged squared distance for `≈_δ`. -/
def stateDependentDistanceError {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) : Error :=
  averageOverDistribution 𝒟 (fun q => questionStateDependentDistanceDefect ψ (A q) (B q))

/-- Averaged defect in strong self-consistency. -/
def strongSelfConsistencyError {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) : Error :=
  averageOverDistribution 𝒟 (fun q => questionStrongSelfConsistencyDefect ψ (A q))

/-- Total mass of a submeasurement on state `ψ`, computed from the concrete total operator. -/
def subMeasurementMass {Outcome : Type*}
    (ψ : QuantumState) (A : SubMeasurement Outcome) : Error :=
  expectationValue ψ A.totalOperator

/-- Averaged total mass of an indexed submeasurement. -/
def indexedSubMeasurementMass {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) : Error :=
  averageOverDistribution 𝒟 (fun q => subMeasurementMass ψ (A q))

/-- Defect in domination by an operator witness, measured at the expectation-value level. -/
def boundednessError {Outcome : Type*}
    (ψ : QuantumState) (A : SubMeasurement Outcome) (Z : Operator) : Error :=
  max 0 (subMeasurementMass ψ A - expectationValue ψ Z)

/-- Consistency relation. -/
structure ConsistencyRel {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (δ : Error) : Prop where
  offDiagonalBound : consistencyError ψ 𝒟 A B ≤ δ

/-- State-dependent distance relation. -/
structure StateDependentDistanceRel {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (δ : Error) : Prop where
  squaredDistanceBound : stateDependentDistanceError ψ 𝒟 A B ≤ δ

/-- Strong self-consistency relation. -/
structure StrongSelfConsistencyRel {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) (δ : Error) : Prop where
  diagonalOverlapBound : strongSelfConsistencyError ψ 𝒟 A ≤ δ

/-- Completeness statement for a submeasurement. -/
structure CompletenessAtLeast {Outcome : Type*}
    (ψ : QuantumState) (A : SubMeasurement Outcome) (r : Error) : Prop where
  lowerBound : subMeasurementMass ψ A ≥ r

/-- Boundedness statement witnessed by an operator. -/
structure BoundedByOperator {Outcome : Type*}
    (ψ : QuantumState) (A : SubMeasurement Outcome) (Z : Operator) (δ : Error) : Prop where
  witnessPositiveSemidefinite : PositiveSemidefinite Z
  upperBound : boundednessError ψ A Z ≤ δ

/-- Consistency between a points measurement and a global polynomial submeasurement. -/
structure ConsistentWithPolynomialEvaluation (params : Parameters)
    (ψ : QuantumState)
    (A : IndexedSubMeasurement (Point params) (Fq params))
    (G : SubMeasurement (Polynomial params))
    (δ : Error) : Prop where
  evaluationConsistency :
    ConsistencyRel ψ (uniformDistribution (Point params))
      A
      (polynomialEvaluationFamily params G)
      δ

/-- Consistency between two global polynomial submeasurements. -/
structure PolynomialMeasurementsConsistent (params : Parameters)
    (ψ : QuantumState)
    (G₁ G₂ : SubMeasurement (Polynomial params))
    (δ : Error) : Prop where
  mutualConsistency :
    ConsistencyRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily G₁)
      (constantSubMeasurementFamily G₂)
      δ

/-- Strong self-consistency for a global polynomial submeasurement. -/
structure PolynomialMeasurementStronglySelfConsistent (params : Parameters)
    (ψ : QuantumState) (G : SubMeasurement (Polynomial params)) (_δ : Error) : Prop where
  diagonalMassBound :
    StrongSelfConsistencyRel ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily G)
      _δ

end MIPStarRE.LDT
