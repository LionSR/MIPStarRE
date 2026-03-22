import Mathlib

/-!
Matching scaffold for Section 3 of the low individual degree paper in
`references/ldt-paper/test_definition.tex`.

This file intentionally uses lightweight paper-local placeholders. The goal of the
current pass is to mirror the paper's declarations closely enough that the
blueprint can target stable Lean names before any proofs are attempted.
-/

namespace MIPStarRE.Paper2009LDT

abbrev Error := ℝ

inductive Role where
  | A
  | B
  deriving DecidableEq, Repr, Inhabited

def Role.other : Role → Role
  | .A => .B
  | .B => .A

@[simp] theorem Role.other_other (r : Role) : r.other.other = r := by
  cases r <;> rfl

/-- Parameters for the `(m,q,d)` low individual degree test. -/
structure Parameters where
  m : ℕ
  q : ℕ
  d : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- The successor test obtained by appending one coordinate. -/
def Parameters.next (params : Parameters) : Parameters :=
  { params with m := params.m + 1 }

abbrev Fq (params : Parameters) := Fin params.q
abbrev Point (params : Parameters) := Fin params.m → Fq params
abbrev PointTuple (params : Parameters) (k : ℕ) := Fin k → Fq params

/-- The zero coordinate extracted from any available field element witness. -/
def zeroCoord {params : Parameters} (x : Fq params) : Fq params :=
  let hq : 0 < params.q :=
    Nat.lt_of_lt_of_le (Nat.zero_lt_succ x.1) (Nat.succ_le_of_lt x.isLt)
  ⟨0, hq⟩

/-- Append a final coordinate to a point in `F_q^m`. -/
def appendPoint (params : Parameters) (u : Point params) (x : Fq params) : Point params.next :=
  fun i => if h : i.1 < params.m then u ⟨i.1, h⟩ else x

/-- Truncate the last coordinate of a point in `F_q^{m+1}`. -/
def truncatePoint (params : Parameters) (u : Point params.next) : Point params :=
  fun i => u ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self params.m)⟩

/-- Extract the final coordinate of a point in `F_q^{m+1}`. -/
def pointHeight (params : Parameters) (u : Point params.next) : Fq params :=
  u ⟨params.m, Nat.lt_succ_self params.m⟩

@[simp] theorem truncatePoint_appendPoint (params : Parameters)
    (u : Point params) (x : Fq params) :
    truncatePoint params (appendPoint params u x) = u := by
  funext i
  simp [truncatePoint, appendPoint, i.2]

@[simp] theorem pointHeight_appendPoint (params : Parameters)
    (u : Point params) (x : Fq params) :
    pointHeight params (appendPoint params u x) = x := by
  simp [pointHeight, appendPoint]

/-- A lightweight encoding of an axis-parallel line in `F_q^m`. -/
structure AxisParallelLine (params : Parameters) where
  base : Point params
  direction : Fin params.m

/-- Embed an axis-parallel line into the slice at height `x`. -/
def AxisParallelLine.appendAtHeight (params : Parameters)
    (ℓ : AxisParallelLine params) (x : Fq params) : AxisParallelLine params.next where
  base := appendPoint params ℓ.base x
  direction := ⟨ℓ.direction.1, Nat.lt_trans ℓ.direction.2 (Nat.lt_succ_self params.m)⟩

/-- A lightweight encoding of a diagonal line in `F_q^m`. -/
structure DiagonalLine (params : Parameters) where
  base : Point params
  direction : Point params

/-- Embed a diagonal line into the slice at height `x`. -/
def DiagonalLine.appendAtHeight (params : Parameters)
    (ℓ : DiagonalLine params) (x : Fq params) : DiagonalLine params.next where
  base := appendPoint params ℓ.base x
  direction := appendPoint params ℓ.direction (zeroCoord x)

/-- Global low-individual-degree polynomial outcomes. -/
structure Polynomial (params : Parameters) where
  toFun : Point params → Fq params
  lowIndividualDegree : True

instance {params : Parameters} : CoeFun (Polynomial params) (fun _ => Point params → Fq params) :=
  ⟨Polynomial.toFun⟩

/-- Axis-parallel line answers with an explicit degree-bound witness slot. -/
structure AxisLinePolynomial (params : Parameters) where
  toFun : Point params → Fq params
  supportedOnAxisLine : True
  degreeBounded : True

instance {params : Parameters} :
    CoeFun (AxisLinePolynomial params) (fun _ => Point params → Fq params) :=
  ⟨AxisLinePolynomial.toFun⟩

/-- Diagonal-line answers with an explicit degree-bound witness slot. -/
structure DiagonalLinePolynomial (params : Parameters) where
  toFun : Point params → Fq params
  supportedOnDiagonalLine : True
  degreeBounded : True

instance {params : Parameters} :
    CoeFun (DiagonalLinePolynomial params) (fun _ => Point params → Fq params) :=
  ⟨DiagonalLinePolynomial.toFun⟩

/-- Extend a global polynomial to the slice at height `x`. -/
def Polynomial.appendAtHeight (params : Parameters)
    (g : Polynomial params) (_x : Fq params) : Polynomial params.next where
  toFun := fun u => g (truncatePoint params u)
  lowIndividualDegree := trivial

/-- Restrict a global polynomial in `m + 1` variables to the slice at height `x`. -/
def Polynomial.restrictAtHeight (params : Parameters)
    (g : Polynomial params.next) (x : Fq params) : Polynomial params where
  toFun := fun u => g (appendPoint params u x)
  lowIndividualDegree := trivial

/-- Extend an axis-line answer to the slice at height `x`. -/
def AxisLinePolynomial.appendAtHeight (params : Parameters)
    (f : AxisLinePolynomial params) (_x : Fq params) : AxisLinePolynomial params.next where
  toFun := fun u => f (truncatePoint params u)
  supportedOnAxisLine := trivial
  degreeBounded := trivial

/-- Restrict an axis-line answer in `m + 1` variables to the slice at height `x`. -/
def AxisLinePolynomial.restrictAtHeight (params : Parameters)
    (f : AxisLinePolynomial params.next) (x : Fq params) : AxisLinePolynomial params where
  toFun := fun u => f (appendPoint params u x)
  supportedOnAxisLine := trivial
  degreeBounded := trivial

/-- Extend a diagonal-line answer to the slice at height `x`. -/
def DiagonalLinePolynomial.appendAtHeight (params : Parameters)
    (f : DiagonalLinePolynomial params) (_x : Fq params) : DiagonalLinePolynomial params.next where
  toFun := fun u => f (truncatePoint params u)
  supportedOnDiagonalLine := trivial
  degreeBounded := trivial

/-- Restrict a diagonal-line answer in `m + 1` variables to the slice at height `x`. -/
def DiagonalLinePolynomial.restrictAtHeight (params : Parameters)
    (f : DiagonalLinePolynomial params.next) (x : Fq params) : DiagonalLinePolynomial params where
  toFun := fun u => f (appendPoint params u x)
  supportedOnDiagonalLine := trivial
  degreeBounded := trivial

/-- Placeholder for a bipartite state. -/
structure QuantumState where
  name : String := ""
  deriving Inhabited, Repr

/-- Placeholder for an operator or matrix expression. -/
structure Operator where
  name : String := ""
  deriving Inhabited, Repr, DecidableEq

/-- Placeholder for a probability distribution. -/
structure Distribution (α : Type _) where
  name : String := ""
  deriving Inhabited, Repr

/-- The uniform distribution placeholder on a given type. -/
def uniformDistribution (α : Type _) : Distribution α where
  name := "uniform"

/-- Placeholder total variation distance. -/
def totalVariationDistance {α : Type _} (_μ _ν : Distribution α) : Error := 0

/-- Abstract positive semidefiniteness predicate. -/
structure PositiveSemidefinite (_Z : Operator) : Prop where
  nonnegativeWitness : True

/-- A paper-local submeasurement with outcomes in `α`. -/
structure SubMeasurement (α : Type _) where
  name : String := ""
  outcomeOperator : α → Operator := fun _ => default
  totalOperator : Operator := default
  deriving Inhabited

/-- A paper-local measurement. -/
structure Measurement (α : Type _) extends SubMeasurement α where
  completeWitness : True := trivial
  deriving Inhabited

/-- A paper-local projective submeasurement. -/
structure ProjectiveSubMeasurement (α : Type _) extends SubMeasurement α where
  projectiveWitness : True := trivial
  deriving Inhabited

/-- A paper-local projective measurement. -/
structure ProjectiveMeasurement (α : Type _) extends Measurement α where
  projectiveWitness : True := trivial
  deriving Inhabited

abbrev IndexedSubMeasurement (Question Outcome : Type _) := Question → SubMeasurement Outcome
abbrev IndexedMeasurement (Question Outcome : Type _) := Question → Measurement Outcome
abbrev IndexedProjectiveSubMeasurement (Question Outcome : Type _) :=
  Question → ProjectiveSubMeasurement Outcome
abbrev IndexedProjectiveMeasurement (Question Outcome : Type _) :=
  Question → ProjectiveMeasurement Outcome

namespace IndexedMeasurement

def toIndexedSubMeasurement {Question Outcome : Type _}
    (A : IndexedMeasurement Question Outcome) : IndexedSubMeasurement Question Outcome :=
  fun q => (A q).toSubMeasurement

end IndexedMeasurement

namespace IndexedProjectiveSubMeasurement

def toIndexedSubMeasurement {Question Outcome : Type _}
    (A : IndexedProjectiveSubMeasurement Question Outcome) :
    IndexedSubMeasurement Question Outcome :=
  fun q => (A q).toSubMeasurement

end IndexedProjectiveSubMeasurement

namespace IndexedProjectiveMeasurement

def toIndexedMeasurement {Question Outcome : Type _}
    (A : IndexedProjectiveMeasurement Question Outcome) :
    IndexedMeasurement Question Outcome :=
  fun q => (A q).toMeasurement

def toIndexedSubMeasurement {Question Outcome : Type _}
    (A : IndexedProjectiveMeasurement Question Outcome) :
    IndexedSubMeasurement Question Outcome :=
  fun q => (A q).toSubMeasurement

end IndexedProjectiveMeasurement

/-- Post-process the outcomes of a submeasurement. -/
def postprocess {α β : Type _} (A : SubMeasurement α) (_f : α → β) : SubMeasurement β where
  name := s!"{A.name}.post"
  outcomeOperator := fun _ => { name := s!"{A.name}.post.outcome" }
  totalOperator := A.totalOperator

/-- Complete a submeasurement by adjoining a distinguished failure outcome. -/
def completeSubMeasurement {α : Type _} (A : SubMeasurement α) : Measurement (Option α) where
  toSubMeasurement := {
    name := s!"{A.name}.completion"
    outcomeOperator := fun
      | some a => A.outcomeOperator a
      | none => { name := s!"{A.name}.failure" }
    totalOperator := { name := s!"{A.name}.completion.total" }
  }

/-- Constant indexed family taking the same submeasurement on every question. -/
def constantSubMeasurementFamily {α : Type _} (A : SubMeasurement α) :
    IndexedSubMeasurement Unit α :=
  fun _ => A

/-- Evaluate a polynomial-valued submeasurement at a point. -/
def evaluateAt (params : Parameters) (u : Point params)
    (G : SubMeasurement (Polynomial params)) : SubMeasurement (Fq params) :=
  postprocess G (fun g => g u)

/-- View a global polynomial submeasurement as a point-indexed answer family. -/
def polynomialEvaluationFamily (params : Parameters)
    (G : SubMeasurement (Polynomial params)) :
    IndexedSubMeasurement (Point params) (Fq params) :=
  fun u => evaluateAt params u G

/-- Evaluate each member of an indexed polynomial family at the same point. -/
def evaluateFiberFamilyAt (params : Parameters) (u : Point params)
    (G : IndexedSubMeasurement (Fq params) (Polynomial params)) :
    IndexedSubMeasurement (Fq params) (Fq params) :=
  fun x => evaluateAt params u (G x)

/-- Evaluate an indexed slice family at a point `(u, x)` in `F_q^{m+1}`. -/
def evaluateFiberFamilyAtNextPoint (params : Parameters)
    (G : IndexedSubMeasurement (Fq params) (Polynomial params)) :
    IndexedSubMeasurement (Point params.next) (Fq params) :=
  fun u => evaluateAt params (truncatePoint params u) (G (pointHeight params u))

/-- Placeholder averaged off-diagonal mass for consistency statements. -/
def consistencyError {Question Outcome : Type _}
    (_ψ : QuantumState) (_𝒟 : Distribution Question)
    (_A _B : IndexedSubMeasurement Question Outcome) : Error := 0

/-- Placeholder averaged squared distance for `≈_δ`. -/
def stateDependentDistanceError {Question Outcome : Type _}
    (_ψ : QuantumState) (_𝒟 : Distribution Question)
    (_A _B : IndexedSubMeasurement Question Outcome) : Error := 0

/-- Placeholder defect in strong self-consistency. -/
def strongSelfConsistencyError {Question Outcome : Type _}
    (_ψ : QuantumState) (_𝒟 : Distribution Question)
    (_A : IndexedSubMeasurement Question Outcome) : Error := 0

/-- Placeholder total mass of a submeasurement on state `ψ`. -/
def subMeasurementMass {Outcome : Type _}
    (_ψ : QuantumState) (_A : SubMeasurement Outcome) : Error := 0

/-- Placeholder averaged total mass of an indexed submeasurement. -/
def indexedSubMeasurementMass {Question Outcome : Type _}
    (_ψ : QuantumState) (_𝒟 : Distribution Question)
    (_A : IndexedSubMeasurement Question Outcome) : Error := 0

/-- Placeholder defect for domination by an operator witness. -/
def boundednessError {Outcome : Type _}
    (_ψ : QuantumState) (_A : SubMeasurement Outcome) (_Z : Operator) : Error := 0

/-- Placeholder consistency relation. -/
structure ConsistencyRel {Question Outcome : Type _}
    (_ψ : QuantumState) (_𝒟 : Distribution Question)
    (_A _B : IndexedSubMeasurement Question Outcome) (_δ : Error) : Prop where
  offDiagonalBound : consistencyError _ψ _𝒟 _A _B ≤ _δ

/-- Placeholder state-dependent distance relation. -/
structure StateDependentDistanceRel {Question Outcome : Type _}
    (_ψ : QuantumState) (_𝒟 : Distribution Question)
    (_A _B : IndexedSubMeasurement Question Outcome) (_δ : Error) : Prop where
  squaredDistanceBound : stateDependentDistanceError _ψ _𝒟 _A _B ≤ _δ

/-- Placeholder strong self-consistency relation. -/
structure StrongSelfConsistencyRel {Question Outcome : Type _}
    (_ψ : QuantumState) (_𝒟 : Distribution Question)
    (_A : IndexedSubMeasurement Question Outcome) (_δ : Error) : Prop where
  diagonalOverlapBound : strongSelfConsistencyError _ψ _𝒟 _A ≤ _δ

/-- Placeholder completeness statement for a submeasurement. -/
structure CompletenessAtLeast {Outcome : Type _}
    (_ψ : QuantumState) (_A : SubMeasurement Outcome) (_r : Error) : Prop where
  lowerBound : subMeasurementMass _ψ _A ≥ _r

/-- Placeholder boundedness statement witnessed by an operator. -/
structure BoundedByOperator {Outcome : Type _}
    (_ψ : QuantumState) (_A : SubMeasurement Outcome) (_Z : Operator) (_δ : Error) : Prop where
  upperBound : boundednessError _ψ _A _Z ≤ _δ

/-- Placeholder consistency between a points measurement and a global polynomial submeasurement. -/
structure ConsistentWithPolynomialEvaluation (params : Parameters)
    (_ψ : QuantumState)
    (_A : IndexedSubMeasurement (Point params) (Fq params))
    (_G : SubMeasurement (Polynomial params))
    (_δ : Error) : Prop where
  evaluationConsistency :
    ConsistencyRel _ψ (uniformDistribution (Point params))
      _A
      (polynomialEvaluationFamily params _G)
      _δ

/-- Placeholder consistency between two global polynomial submeasurements. -/
structure PolynomialMeasurementsConsistent (params : Parameters)
    (_ψ : QuantumState)
    (_G₁ _G₂ : SubMeasurement (Polynomial params))
    (_δ : Error) : Prop where
  mutualConsistency :
    ConsistencyRel _ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily _G₁)
      (constantSubMeasurementFamily _G₂)
      _δ

/-- Placeholder strong self-consistency for a global polynomial submeasurement. -/
structure PolynomialMeasurementStronglySelfConsistent (params : Parameters)
    (_ψ : QuantumState) (_G : SubMeasurement (Polynomial params)) (_δ : Error) : Prop where
  diagonalMassBound :
    StrongSelfConsistencyRel _ψ (uniformDistribution Unit)
      (constantSubMeasurementFamily _G)
      _δ

/-- Paper-local symmetric strategy data. -/
structure SymmetricStrategy (params : Parameters) where
  state : QuantumState
  pointMeasurement : IndexedProjectiveMeasurement (Point params) (Fq params)
  axisParallelMeasurement :
    IndexedProjectiveMeasurement (AxisParallelLine params) (AxisLinePolynomial params)
  diagonalMeasurement :
    IndexedProjectiveMeasurement (DiagonalLine params) (DiagonalLinePolynomial params)
  deriving Inhabited

/-- Paper-local (not necessarily symmetric) projective strategy data. -/
structure ProjectiveStrategy (params : Parameters) where
  state : QuantumState
  pointMeasurementA : IndexedProjectiveMeasurement (Point params) (Fq params)
  axisParallelMeasurementA :
    IndexedProjectiveMeasurement (AxisParallelLine params) (AxisLinePolynomial params)
  diagonalMeasurementA :
    IndexedProjectiveMeasurement (DiagonalLine params) (DiagonalLinePolynomial params)
  pointMeasurementB : IndexedProjectiveMeasurement (Point params) (Fq params)
  axisParallelMeasurementB :
    IndexedProjectiveMeasurement (AxisParallelLine params) (AxisLinePolynomial params)
  diagonalMeasurementB :
    IndexedProjectiveMeasurement (DiagonalLine params) (DiagonalLinePolynomial params)
  deriving Inhabited

namespace SymmetricStrategy

/-- Placeholder failure probability in the axis-parallel lines test. -/
def axisParallelFailureProbability {params : Parameters}
    (_strategy : SymmetricStrategy params) : Error := 0

/-- Placeholder failure probability in the self-consistency test. -/
def selfConsistencyFailureProbability {params : Parameters}
    (_strategy : SymmetricStrategy params) : Error := 0

/-- Placeholder failure probability in the diagonal lines test. -/
def diagonalFailureProbability {params : Parameters}
    (_strategy : SymmetricStrategy params) : Error := 0

/-- Placeholder for the paper's notion of an `(ε,δ,γ)`-good symmetric strategy. -/
structure IsGood {params : Parameters} (strategy : SymmetricStrategy params)
    (eps delta gamma : Error) : Prop where
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end SymmetricStrategy

namespace ProjectiveStrategy

/-- Placeholder failure probability for the full low-individual-degree test. -/
def lowIndividualDegreeFailureProbability {params : Parameters}
    (_strategy : ProjectiveStrategy params) : Error := 0

/-- Placeholder for passing the full low-individual-degree test with error `ε`. -/
structure PassesLowIndividualDegreeTest {params : Parameters}
    (strategy : ProjectiveStrategy params) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

end ProjectiveStrategy

/-- A packaged family `x ↦ G^x` together with its witness operators. -/
structure IndexedPolynomialFamily (params : Parameters) where
  meas : IndexedProjectiveSubMeasurement (Fq params) (Polynomial params)
  witness : Fq params → Operator := fun _ => default
  deriving Inhabited

namespace IndexedPolynomialFamily

/-- Placeholder averaged submeasurement `G = E_x G^x` from the paper. -/
def averagedSubMeasurement {params : Parameters}
    (_family : IndexedPolynomialFamily params) : SubMeasurement (Polynomial params) where
  name := s!"Gavg({params.m},{params.q},{params.d})"
  outcomeOperator := fun _ => { name := s!"Gavg({params.m},{params.q},{params.d}).outcome" }
  totalOperator := { name := s!"Gavg({params.m},{params.q},{params.d}).total" }

/-- Evaluate the slice family at a point `(u, x)` in `F_q^{m+1}`. -/
def evaluatedAtNextPoint {params : Parameters}
    (family : IndexedPolynomialFamily params) :
    IndexedSubMeasurement (Point params.next) (Fq params) :=
  fun u =>
    evaluateAt params (truncatePoint params u)
      ((family.meas (pointHeight params u)).toSubMeasurement)

structure Complete {params : Parameters} (family : IndexedPolynomialFamily params)
    (ψ : QuantumState) (kappa : Error) : Prop where
  averageCompleteness :
    CompletenessAtLeast ψ family.averagedSubMeasurement (1 - kappa)

structure ConsistentWithPoints {params : Parameters} (family : IndexedPolynomialFamily params)
    (strategy : SymmetricStrategy params.next) (zeta : Error) : Prop where
  pointConsistency :
    ConsistencyRel strategy.state (uniformDistribution (Point params.next))
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      family.evaluatedAtNextPoint
      zeta

structure StronglySelfConsistent {params : Parameters} (family : IndexedPolynomialFamily params)
    (ψ : QuantumState) (zeta : Error) : Prop where
  sliceSelfConsistency :
    StrongSelfConsistencyRel ψ (uniformDistribution (Fq params))
      (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement family.meas)
      zeta

structure Bounded {params : Parameters} (family : IndexedPolynomialFamily params)
    (ψ : QuantumState) (zeta : Error) : Prop where
  slicePositiveSemidefinite : ∀ x, PositiveSemidefinite (family.witness x)
  sliceBoundedness :
    ∀ x, BoundedByOperator ψ ((family.meas x).toSubMeasurement) (family.witness x) zeta

end IndexedPolynomialFamily

namespace Section3Test

/-- The explicit `ν` from `thm:main-formal`, recorded with the paper's formula. -/
noncomputable def mainFormalError (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) *
    (Real.rpow eps (1 / (40000 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (40000 : Error)) +
      Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))))

/--
`thm:main-formal` from `test_definition.tex`.

This matching declaration keeps the paper's main output shape: two global polynomial
measurements, one for each prover, consistent with the point measurements and with
 each other.
-/
theorem mainFormal
    (params : Parameters)
    (strategy : ProjectiveStrategy params)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ) :
    ∃ G_A G_B : ProjectiveMeasurement (Polynomial params),
      ConsistentWithPolynomialEvaluation params strategy.state
          (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurementA)
          G_B.toSubMeasurement
          (mainFormalError params k eps) ∧
        ConsistentWithPolynomialEvaluation params strategy.state
          (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurementB)
          G_A.toSubMeasurement
          (mainFormalError params k eps) ∧
        PolynomialMeasurementsConsistent params strategy.state
          G_A.toSubMeasurement
          G_B.toSubMeasurement
          (mainFormalError params k eps) := by
  sorry

end Section3Test

end MIPStarRE.Paper2009LDT
