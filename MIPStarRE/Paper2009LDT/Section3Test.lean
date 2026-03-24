import Mathlib
import MIPStarRE.Paper2009LDT.Basic.Distribution
import MIPStarRE.Paper2009LDT.Basic.SubMeasurement

/-!
Matching scaffold for Section 3 of the low individual degree paper in
`references/ldt-paper/test_definition.tex`.

This pass keeps the theorem statements lightweight, but it now makes three parts of
Section 3 materially more honest:

* the ambient alphabet carries a genuine finite-ring coding layer via `ZMod q`, and
  the optional prime-power witness is wired to Mathlib's `GaloisField`;
* global and line answers are represented by actual multivariate / univariate
  polynomial data, not by arbitrary tagged functions;
* the state / operator layer reuses the local finite-dimensional matrix API for the
  ambient operator carrier and expectation values.

The remaining gaps are recorded explicitly in the comparison-calculus layer and the
later theorem proofs, which are still scaffolded with `sorry`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.Paper2009LDT

/-- Re-encode a scalar in `ZMod q` as its canonical representative in `Fin q`. -/
def encodeScalar {params : Parameters} (x : Scalar params) : Fq params :=
  ⟨x.val, ZMod.val_lt x⟩

/-- The zero coordinate. -/
def zeroCoord {params : Parameters} : Fq params :=
  encodeScalar 0

/-- Coordinate addition transported through the `Fin q` coding. -/
def addCoord {params : Parameters} (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x + decodeScalar y)

/-- Coordinate subtraction transported through the `Fin q` coding. -/
def subCoord {params : Parameters} (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x - decodeScalar y)

/-- Coordinate multiplication transported through the `Fin q` coding. -/
def mulCoord {params : Parameters} (x y : Fq params) : Fq params :=
  encodeScalar (decodeScalar x * decodeScalar y)

/-- Pointwise addition in the coded ambient space. -/
def addPoint {params : Parameters} (u v : Point params) : Point params :=
  fun i => addCoord (u i) (v i)

/-- Scalar multiplication in the coded ambient space. -/
def smulPoint {params : Parameters} (t : Fq params) (u : Point params) : Point params :=
  fun i => mulCoord t (u i)

/-- The inclusion of the first `m` coordinates into `m + 1` coordinates. -/
def embedCoord (params : Parameters) : Fin params.m → Fin params.next.m :=
  fun i => ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self params.m)⟩

/-- The last coordinate of `F_q^(m+1)`. -/
def lastCoord (params : Parameters) : Fin params.next.m :=
  ⟨params.m, Nat.lt_succ_self params.m⟩

/-- Append a final coordinate to a point in `F_q^m`. -/
def appendPoint (params : Parameters) (u : Point params) (x : Fq params) : Point params.next :=
  fun i => if h : i.1 < params.m then u ⟨i.1, h⟩ else x

/-- Truncate the last coordinate of a point in `F_q^{m+1}`. -/
def truncatePoint (params : Parameters) (u : Point params.next) : Point params :=
  fun i => u ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self params.m)⟩

/-- Extract the final coordinate of a point in `F_q^{m+1}`. -/
def pointHeight (params : Parameters) (u : Point params.next) : Fq params :=
  u (lastCoord params)

@[simp] theorem truncatePoint_appendPoint (params : Parameters)
    (u : Point params) (x : Fq params) :
    truncatePoint params (appendPoint params u x) = u := by
  funext i
  simp [truncatePoint, appendPoint, i.2]

@[simp] theorem pointHeight_appendPoint (params : Parameters)
    (u : Point params) (x : Fq params) :
    pointHeight params (appendPoint params u x) = x := by
  simp [pointHeight, lastCoord, appendPoint]

/-- Decode a coded point as a tuple of `ZMod q` scalars. -/
def decodePoint {params : Parameters} (u : Point params) : Fin params.m → Scalar params :=
  fun i => decodeScalar (u i)

/-- Evaluate a multivariate `ZMod q` polynomial on a coded point. -/
def evalPolynomialModel (params : Parameters)
    (p : PolynomialModel params) (u : Point params) : Fq params :=
  encodeScalar (MvPolynomial.eval (decodePoint u) p)

/-- Evaluate a univariate `ZMod q` polynomial on a coded point. -/
def evalLinePolynomialModel (params : Parameters)
    (p : LinePolynomialModel params) (t : Fq params) : Fq params :=
  encodeScalar (_root_.Polynomial.eval (decodeScalar t) p)

/-- A genuinely axis-parallel affine line in `F_q^m`. -/
structure AxisParallelLine (params : Parameters) where
  base : Point params
  direction : Fin params.m
  deriving DecidableEq, Inhabited

namespace AxisParallelLine

/-- The canonical affine parameterization `t ↦ base + t e_i`. -/
def pointAt {params : Parameters} (ℓ : AxisParallelLine params) : Fq params → Point params :=
  fun t i =>
    if i = ℓ.direction then
      addCoord (ℓ.base i) t
    else
      ℓ.base i

/-- Embed an axis-parallel line into the slice at height `x`. -/
def appendAtHeight (params : Parameters)
    (ℓ : AxisParallelLine params) (x : Fq params) : AxisParallelLine params.next where
  base := appendPoint params ℓ.base x
  direction := embedCoord params ℓ.direction

end AxisParallelLine

/-- A genuinely affine diagonal line in `F_q^m`. -/
structure DiagonalLine (params : Parameters) where
  base : Point params
  direction : Point params
  deriving DecidableEq, Inhabited

namespace DiagonalLine

/-- The canonical affine parameterization `t ↦ base + t · direction`. -/
def pointAt {params : Parameters} (ℓ : DiagonalLine params) : Fq params → Point params :=
  fun t => addPoint ℓ.base (smulPoint t ℓ.direction)

/-- Embed a diagonal line into the slice at height `x`, keeping the new coordinate fixed. -/
def appendAtHeight (params : Parameters)
    (ℓ : DiagonalLine params) (x : Fq params) : DiagonalLine params.next where
  base := appendPoint params ℓ.base x
  direction := appendPoint params ℓ.direction zeroCoord

end DiagonalLine

/-- A coded function has low individual degree when it is represented by an actual
multivariate polynomial over `ZMod q` whose degree in each variable is at most `d`. -/
def HasLowIndividualDegree (params : Parameters) (g : Point params → Fq params) : Prop :=
  ∃ p : PolynomialModel params,
    (∀ i, MvPolynomial.degreeOf i p ≤ params.d) ∧
      g = evalPolynomialModel params p

/-- A coded univariate function has degree at most `bound` when it is represented by
an actual polynomial over `ZMod q` of degree at most `bound`. -/
def HasUnivariateDegreeAtMost (params : Parameters)
    (bound : ℕ) (f : Fq params → Fq params) : Prop :=
  ∃ p : LinePolynomialModel params,
    p.natDegree ≤ bound ∧
      f = evalLinePolynomialModel params p

/-- Axis-parallel line answers are genuine univariate degree-`d` polynomials. -/
structure AxisLinePolynomial (params : Parameters) where
  poly : LinePolynomialModel params
  degreeBounded : poly.natDegree ≤ params.d

namespace AxisLinePolynomial

/-- Evaluation of an axis-line answer on the line parameter. -/
def toFun {params : Parameters} (f : AxisLinePolynomial params) : Fq params → Fq params :=
  evalLinePolynomialModel params f.poly

instance {params : Parameters} :
    CoeFun (AxisLinePolynomial params) (fun _ => Fq params → Fq params) :=
  ⟨AxisLinePolynomial.toFun⟩

/-- The stored polynomial really witnesses the advertised degree bound. -/
theorem hasUnivariateDegreeAtMost {params : Parameters} (f : AxisLinePolynomial params) :
    HasUnivariateDegreeAtMost params params.d f := by
  refine ⟨f.poly, f.degreeBounded, ?_⟩
  funext t
  rfl

/-- Extend an axis-line answer to the slice at height `x`. -/
def appendAtHeight (params : Parameters)
    (f : AxisLinePolynomial params) (_x : Fq params) : AxisLinePolynomial params.next where
  poly := f.poly
  degreeBounded := by
    simpa [Parameters.next] using f.degreeBounded

/-- Restrict an axis-line answer in `m + 1` variables to the slice at height `x`. -/
def restrictAtHeight (params : Parameters)
    (f : AxisLinePolynomial params.next) (_x : Fq params) : AxisLinePolynomial params where
  poly := f.poly
  degreeBounded := by
    simpa [Parameters.next] using f.degreeBounded

end AxisLinePolynomial

/-- Diagonal-line answers are genuine univariate degree-`md` polynomials. -/
structure DiagonalLinePolynomial (params : Parameters) where
  poly : LinePolynomialModel params
  degreeBounded : poly.natDegree ≤ params.m * params.d

namespace DiagonalLinePolynomial

/-- Evaluation of a diagonal-line answer on the line parameter. -/
def toFun {params : Parameters} (f : DiagonalLinePolynomial params) : Fq params → Fq params :=
  evalLinePolynomialModel params f.poly

instance {params : Parameters} :
    CoeFun (DiagonalLinePolynomial params) (fun _ => Fq params → Fq params) :=
  ⟨DiagonalLinePolynomial.toFun⟩

/-- The stored polynomial really witnesses the advertised degree bound. -/
theorem hasUnivariateDegreeAtMost {params : Parameters} (f : DiagonalLinePolynomial params) :
    HasUnivariateDegreeAtMost params (params.m * params.d) f := by
  refine ⟨f.poly, f.degreeBounded, ?_⟩
  funext t
  rfl

/-- Extend a diagonal-line answer to the slice at height `x`. -/
def appendAtHeight (params : Parameters)
    (f : DiagonalLinePolynomial params) (_x : Fq params) : DiagonalLinePolynomial params.next where
  poly := f.poly
  degreeBounded := by
    exact le_trans f.degreeBounded (Nat.mul_le_mul_right _ (Nat.le_succ _))

/-- Restrict a diagonal-line answer in `m + 1` variables to the slice at height `x`.
This interface now makes the stronger slice-wise degree requirement explicit. -/
def restrictAtHeight (params : Parameters)
    (f : DiagonalLinePolynomial params.next) (_x : Fq params)
    (hdegree : f.poly.natDegree ≤ params.m * params.d) : DiagonalLinePolynomial params where
  poly := f.poly
  degreeBounded := hdegree

end DiagonalLinePolynomial

/-- Global low-individual-degree polynomial outcomes. -/
structure Polynomial (params : Parameters) where
  poly : PolynomialModel params
  lowIndividualDegree : ∀ i, MvPolynomial.degreeOf i poly ≤ params.d

namespace Polynomial

/-- Evaluation of the stored multivariate polynomial on a coded point. -/
def toFun {params : Parameters} (g : Polynomial params) : Point params → Fq params :=
  evalPolynomialModel params g.poly

instance {params : Parameters} : CoeFun (Polynomial params) (fun _ => Point params → Fq params) :=
  ⟨Polynomial.toFun⟩

/-- The stored polynomial indeed certifies low individual degree. -/
theorem hasLowIndividualDegree {params : Parameters} (g : Polynomial params) :
    HasLowIndividualDegree params g := by
  refine ⟨g.poly, g.lowIndividualDegree, ?_⟩
  funext u
  rfl

/-- Extend a global polynomial to the slice at height `x` by ignoring the new variable. -/
def appendAtHeight (params : Parameters)
    (g : Polynomial params) (_x : Fq params) : Polynomial params.next where
  poly := MvPolynomial.rename (embedCoord params) g.poly
  lowIndividualDegree := by
    intro i
    sorry

/-- Coordinate map for restricting a polynomial in `m+1` variables to the slice `X_m = x`. -/
def restrictAtHeightCoordinateMap (params : Parameters) (x : Fq params) :
    Fin params.next.m → PolynomialModel params :=
  fun i =>
    if h : i.1 < params.m then
      MvPolynomial.X ⟨i.1, h⟩
    else
      MvPolynomial.C (decodeScalar x)

/-- Restrict a global polynomial in `m + 1` variables to the slice at height `x`. -/
def restrictAtHeight (params : Parameters)
    (g : Polynomial params.next) (x : Fq params) : Polynomial params where
  poly := MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x) g.poly
  lowIndividualDegree := by
    intro i
    sorry

/-- Coordinate polynomial for restricting to an axis-parallel affine line. -/
def axisCoordinatePolynomial (params : Parameters) (ℓ : AxisParallelLine params) :
    Fin params.m → LinePolynomialModel params :=
  fun i =>
    if i = ℓ.direction then
      _root_.Polynomial.C (decodeScalar (ℓ.base i)) + _root_.Polynomial.X
    else
      _root_.Polynomial.C (decodeScalar (ℓ.base i))

/-- Restrict a global polynomial to an axis-parallel line. -/
def restrictToAxisParallelLine (params : Parameters)
    (g : Polynomial params) (ℓ : AxisParallelLine params) : AxisLinePolynomial params where
  poly := MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ) g.poly
  degreeBounded := by
    sorry

/-- Coordinate polynomial for restricting to a diagonal affine line. -/
def diagonalCoordinatePolynomial (params : Parameters) (ℓ : DiagonalLine params) :
    Fin params.m → LinePolynomialModel params :=
  fun i =>
    _root_.Polynomial.C (decodeScalar (ℓ.base i)) +
      _root_.Polynomial.C (decodeScalar (ℓ.direction i)) * _root_.Polynomial.X

/-- Restrict a global polynomial to a diagonal line. -/
def restrictToDiagonalLine (params : Parameters)
    (g : Polynomial params) (ℓ : DiagonalLine params) : DiagonalLinePolynomial params where
  poly := MvPolynomial.eval₂Hom _root_.Polynomial.C (diagonalCoordinatePolynomial params ℓ) g.poly
  degreeBounded := by
    sorry

end Polynomial

/-- TODO(finite-outcomes): replace these `sorry`-backed bounded-answer enumerations by
explicit coefficient-vector models for the bounded polynomial answer spaces. They are
used so postprocessing can aggregate outcome operators over actual finite fibers. -/
noncomputable instance (params : Parameters) : Fintype (AxisLinePolynomial params) := by
  classical
  sorry

noncomputable instance (params : Parameters) : Fintype (DiagonalLinePolynomial params) := by
  classical
  sorry

noncomputable instance (params : Parameters) : Fintype (Polynomial params) := by
  classical
  sorry

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
noncomputable def questionMatchingMass {Outcome : Type _}
    (ψ : QuantumState) (A B : SubMeasurement Outcome) : Error :=
  sumOverOutcomesOrElse
    (expectationValue ψ (operatorMul A.totalOperator B.totalOperator))
    (fun a => expectationValue ψ (operatorMul (A.outcomeOperator a) (B.outcomeOperator a)))

/-- Questionwise off-diagonal mass surrogate for consistency. -/
noncomputable def questionConsistencyDefect {Outcome : Type _}
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
noncomputable def questionStateDependentDistanceDefect {Outcome : Type _}
    (ψ : QuantumState) (A B : SubMeasurement Outcome) : Error :=
  let totalDiff := operatorDifference A.totalOperator B.totalOperator
  sumOverOutcomesOrElse
    (expectationValue ψ (operatorMul (operatorAdjoint totalDiff) totalDiff))
    (fun a =>
      let diff := operatorDifference (A.outcomeOperator a) (B.outcomeOperator a)
      expectationValue ψ (operatorMul (operatorAdjoint diff) diff))

/-- Questionwise strong self-consistency defect. -/
noncomputable def questionStrongSelfConsistencyDefect {Outcome : Type _}
    (ψ : QuantumState) (A : SubMeasurement Outcome) : Error :=
  let totalMass := expectationValue ψ A.totalOperator
  let coarseDiagonal := expectationValue ψ (operatorMul A.totalOperator A.totalOperator)
  let diagonalMass :=
    sumOverOutcomesOrElse coarseDiagonal
      (fun a => expectationValue ψ (operatorMul (A.outcomeOperator a) (A.outcomeOperator a)))
  max 0 (totalMass - diagonalMass)

/-- Averaged off-diagonal mass for consistency statements. -/
def consistencyError {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) : Error :=
  averageOverDistribution 𝒟 (fun q => questionConsistencyDefect ψ (A q) (B q))

/-- Averaged squared distance for `≈_δ`. -/
def stateDependentDistanceError {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) : Error :=
  averageOverDistribution 𝒟 (fun q => questionStateDependentDistanceDefect ψ (A q) (B q))

/-- Averaged defect in strong self-consistency. -/
def strongSelfConsistencyError {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) : Error :=
  averageOverDistribution 𝒟 (fun q => questionStrongSelfConsistencyDefect ψ (A q))

/-- Total mass of a submeasurement on state `ψ`, computed from the concrete total operator. -/
def subMeasurementMass {Outcome : Type _}
    (ψ : QuantumState) (A : SubMeasurement Outcome) : Error :=
  expectationValue ψ A.totalOperator

/-- Averaged total mass of an indexed submeasurement. -/
def indexedSubMeasurementMass {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) : Error :=
  averageOverDistribution 𝒟 (fun q => subMeasurementMass ψ (A q))

/-- Defect in domination by an operator witness, measured at the expectation-value level. -/
def boundednessError {Outcome : Type _}
    (ψ : QuantumState) (A : SubMeasurement Outcome) (Z : Operator) : Error :=
  max 0 (subMeasurementMass ψ A - expectationValue ψ Z)

/-- Consistency relation. -/
structure ConsistencyRel {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (δ : Error) : Prop where
  offDiagonalBound : consistencyError ψ 𝒟 A B ≤ δ

/-- State-dependent distance relation. -/
structure StateDependentDistanceRel {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (δ : Error) : Prop where
  squaredDistanceBound : stateDependentDistanceError ψ 𝒟 A B ≤ δ

/-- Strong self-consistency relation. -/
structure StrongSelfConsistencyRel {Question Outcome : Type _}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) (δ : Error) : Prop where
  diagonalOverlapBound : strongSelfConsistencyError ψ 𝒟 A ≤ δ

/-- Completeness statement for a submeasurement. -/
structure CompletenessAtLeast {Outcome : Type _}
    (ψ : QuantumState) (A : SubMeasurement Outcome) (r : Error) : Prop where
  lowerBound : subMeasurementMass ψ A ≥ r

/-- Boundedness statement witnessed by an operator. -/
structure BoundedByOperator {Outcome : Type _}
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

/-- Invariance predicate for the symmetric shared state. -/
structure PermutationInvariantState (_ψ : QuantumState) : Prop where
  swapInvariant : True

/-- Paper-local symmetric strategy data. -/
structure SymmetricStrategy (params : Parameters) where
  state : QuantumState
  statePermutationInvariant : PermutationInvariantState state := ⟨trivial⟩
  pointMeasurement : IndexedProjectiveMeasurement (Point params) (Fq params)
  axisParallelMeasurement :
    IndexedProjectiveMeasurement (AxisParallelLine params) (AxisLinePolynomial params)
  diagonalMeasurement :
    IndexedProjectiveMeasurement (DiagonalLine params) (DiagonalLinePolynomial params)

instance {params : Parameters} : Inhabited (SymmetricStrategy params) where
  default := {
    state := default
    statePermutationInvariant := ⟨trivial⟩
    pointMeasurement := default
    axisParallelMeasurement := default
    diagonalMeasurement := default
  }

/-- Encoded samples `(u₀, i, t)` for the axis-parallel lines test. -/
abbrev AxisParallelTestSample (params : Parameters) := Point params × (Fin params.m × Fq params)

/-- Encoded samples `(u₀, v, t)` for the diagonal lines test. -/
abbrev DiagonalTestSample (params : Parameters) := Point params × (Point params × Fq params)

/-- Sampled point answers in the axis-parallel lines test. -/
noncomputable def axisParallelPointAnswerFamily {params : Parameters}
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (AxisParallelTestSample params) (Fq params) :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeasurement

/-- Sampled line answers, evaluated at the sampled parameter, in the axis-parallel lines test. -/
noncomputable def axisParallelLineAnswerFamily {params : Parameters}
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (AxisParallelTestSample params) (Fq params) :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeasurement) (fun g => g s.2.2)

/-- Sampled point answers in the diagonal lines test. -/
noncomputable def diagonalPointAnswerFamily {params : Parameters}
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (DiagonalTestSample params) (Fq params) :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeasurement

/-- Sampled diagonal-line answers, evaluated at the sampled parameter. -/
noncomputable def diagonalLineAnswerFamily {params : Parameters}
    (strategy : SymmetricStrategy params) :
    IndexedSubMeasurement (DiagonalTestSample params) (Fq params) :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.diagonalMeasurement ℓ).toSubMeasurement) (fun g => g s.2.2)

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

/-- Trace-based failure surrogate for the axis-parallel lines test. -/
noncomputable def axisParallelFailureProbability {params : Parameters}
    (strategy : SymmetricStrategy params) : Error :=
  consistencyError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Trace-based failure surrogate for the self-consistency test. -/
noncomputable def selfConsistencyFailureProbability {params : Parameters}
    (strategy : SymmetricStrategy params) : Error :=
  strongSelfConsistencyError strategy.state
    (uniformDistribution (Point params))
    (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)

/-- Trace-based failure surrogate for the diagonal lines test. -/
noncomputable def diagonalFailureProbability {params : Parameters}
    (strategy : SymmetricStrategy params) : Error :=
  consistencyError strategy.state
    (uniformDistribution (DiagonalTestSample params))
    (diagonalPointAnswerFamily strategy)
    (diagonalLineAnswerFamily strategy)

/-- The paper's notion of an `(ε,δ,γ)`-good symmetric strategy. -/
structure IsGood {params : Parameters} (strategy : SymmetricStrategy params)
    (eps delta gamma : Error) : Prop where
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end SymmetricStrategy

namespace ProjectiveStrategy

/-- View the left prover's local data as a symmetric-strategy-style package. -/
def leftAsSymmetric {params : Parameters} (strategy : ProjectiveStrategy params) :
    SymmetricStrategy params where
  state := strategy.state
  pointMeasurement := strategy.pointMeasurementA
  axisParallelMeasurement := strategy.axisParallelMeasurementA
  diagonalMeasurement := strategy.diagonalMeasurementA

/-- View the right prover's local data as a symmetric-strategy-style package. -/
def rightAsSymmetric {params : Parameters} (strategy : ProjectiveStrategy params) :
    SymmetricStrategy params where
  state := strategy.state
  pointMeasurement := strategy.pointMeasurementB
  axisParallelMeasurement := strategy.axisParallelMeasurementB
  diagonalMeasurement := strategy.diagonalMeasurementB

/-- Trace-based failure surrogate for the full low-individual-degree test. -/
noncomputable def lowIndividualDegreeFailureProbability {params : Parameters}
    (strategy : ProjectiveStrategy params) : Error :=
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  let pointAgreement :=
    consistencyError strategy.state
      (uniformDistribution (Point params))
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurementA)
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurementB)
  let axisParallelBranch :=
    pointAgreement
      + (left.axisParallelFailureProbability + right.axisParallelFailureProbability) / 2
  let selfConsistencyBranch :=
    (left.selfConsistencyFailureProbability + right.selfConsistencyFailureProbability) / 2
  let diagonalBranch :=
    (left.diagonalFailureProbability + right.diagonalFailureProbability) / 2
  (axisParallelBranch + selfConsistencyBranch + diagonalBranch) / 3

/-- Passing the full low-individual-degree test with error `ε`. -/
structure PassesLowIndividualDegreeTest {params : Parameters}
    (strategy : ProjectiveStrategy params) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

end ProjectiveStrategy

/-- A packaged family `x ↦ G^x` together with its witness operators and domination targets. -/
structure IndexedPolynomialFamily (params : Parameters) where
  meas : IndexedProjectiveSubMeasurement (Fq params) (Polynomial params)
  witness : Fq params → Operator := fun _ => default
  dominationTarget : Fq params → Polynomial params → Operator := fun _ _ => default
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
  sliceDominatesTarget :
    ∀ x : Fq params, ∀ g : Polynomial params,
      DominatesOperator (family.witness x) (family.dominationTarget x g)

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
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
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
