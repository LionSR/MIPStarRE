import MIPStarRE.LDT.Test.Defs

/-!
# Section 3 — Strategy

Symmetric and projective strategy structures for the low individual degree test,
together with the test-passing and consistency predicates.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.LDT

/-- Invariance predicate for the symmetric shared state. -/
structure PermutationInvariantState {d : ℕ} (_ψ : QuantumState d) : Prop where
  swapInvariant : True

/-- Paper-local symmetric strategy data. -/
structure SymmetricStrategy (params : Parameters) (d : ℕ) where
  state : QuantumState d
  statePermutationInvariant : PermutationInvariantState state := ⟨trivial⟩
  pointMeasurement : IndexedProjectiveMeasurement (Point params) (Fq params) d
  axisParallelMeasurement :
    IndexedProjectiveMeasurement (AxisParallelLine params) (AxisLinePolynomial params) d
  diagonalMeasurement :
    IndexedProjectiveMeasurement (DiagonalLine params) (DiagonalLinePolynomial params) d

instance {params : Parameters} {d : ℕ} : Inhabited (SymmetricStrategy params d) where
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
noncomputable def axisParallelPointAnswerFamily {params : Parameters} {d : ℕ}
    (strategy : SymmetricStrategy params d) :
    IndexedSubMeasurement (AxisParallelTestSample params) (Fq params) d :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeasurement

/-- Sampled line answers, evaluated at the sampled parameter, in the axis-parallel lines test. -/
noncomputable def axisParallelLineAnswerFamily {params : Parameters} {d : ℕ}
    (strategy : SymmetricStrategy params d) :
    IndexedSubMeasurement (AxisParallelTestSample params) (Fq params) d :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeasurement) (fun g => g s.2.2)

/-- Sampled point answers in the diagonal lines test. -/
noncomputable def diagonalPointAnswerFamily {params : Parameters} {d : ℕ}
    (strategy : SymmetricStrategy params d) :
    IndexedSubMeasurement (DiagonalTestSample params) (Fq params) d :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeasurement

/-- Sampled diagonal-line answers, evaluated at the sampled parameter. -/
noncomputable def diagonalLineAnswerFamily {params : Parameters} {d : ℕ}
    (strategy : SymmetricStrategy params d) :
    IndexedSubMeasurement (DiagonalTestSample params) (Fq params) d :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.diagonalMeasurement ℓ).toSubMeasurement) (fun g => g s.2.2)

/-- Paper-local (not necessarily symmetric) projective strategy data. -/
structure ProjectiveStrategy (params : Parameters) (d : ℕ) where
  state : QuantumState d
  pointMeasurementA : IndexedProjectiveMeasurement (Point params) (Fq params) d
  axisParallelMeasurementA :
    IndexedProjectiveMeasurement (AxisParallelLine params) (AxisLinePolynomial params) d
  diagonalMeasurementA :
    IndexedProjectiveMeasurement (DiagonalLine params) (DiagonalLinePolynomial params) d
  pointMeasurementB : IndexedProjectiveMeasurement (Point params) (Fq params) d
  axisParallelMeasurementB :
    IndexedProjectiveMeasurement (AxisParallelLine params) (AxisLinePolynomial params) d
  diagonalMeasurementB :
    IndexedProjectiveMeasurement (DiagonalLine params) (DiagonalLinePolynomial params) d
  deriving Inhabited

namespace SymmetricStrategy

/-- Trace-based failure surrogate for the axis-parallel lines test. -/
noncomputable def axisParallelFailureProbability {params : Parameters} {d : ℕ}
    (strategy : SymmetricStrategy params d) : Error :=
  consistencyError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Trace-based failure surrogate for the self-consistency test. -/
noncomputable def selfConsistencyFailureProbability {params : Parameters} {d : ℕ}
    (strategy : SymmetricStrategy params d) : Error :=
  strongSelfConsistencyError strategy.state
    (uniformDistribution (Point params))
    (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)

/-- Trace-based failure surrogate for the diagonal lines test. -/
noncomputable def diagonalFailureProbability {params : Parameters} {d : ℕ}
    (strategy : SymmetricStrategy params d) : Error :=
  consistencyError strategy.state
    (uniformDistribution (DiagonalTestSample params))
    (diagonalPointAnswerFamily strategy)
    (diagonalLineAnswerFamily strategy)

/-- The paper's notion of an `(ε,δ,γ)`-good symmetric strategy. -/
structure IsGood {params : Parameters} {d : ℕ} (strategy : SymmetricStrategy params d)
    (eps delta gamma : Error) : Prop where
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end SymmetricStrategy

namespace ProjectiveStrategy

/-- View the left prover's local data as a symmetric-strategy-style package. -/
def leftAsSymmetric {params : Parameters} {d : ℕ} (strategy : ProjectiveStrategy params d) :
    SymmetricStrategy params d where
  state := strategy.state
  pointMeasurement := strategy.pointMeasurementA
  axisParallelMeasurement := strategy.axisParallelMeasurementA
  diagonalMeasurement := strategy.diagonalMeasurementA

/-- View the right prover's local data as a symmetric-strategy-style package. -/
def rightAsSymmetric {params : Parameters} {d : ℕ} (strategy : ProjectiveStrategy params d) :
    SymmetricStrategy params d where
  state := strategy.state
  pointMeasurement := strategy.pointMeasurementB
  axisParallelMeasurement := strategy.axisParallelMeasurementB
  diagonalMeasurement := strategy.diagonalMeasurementB

/-- Trace-based failure surrogate for the full low-individual-degree test. -/
noncomputable def lowIndividualDegreeFailureProbability {params : Parameters} {d : ℕ}
    (strategy : ProjectiveStrategy params d) : Error :=
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
structure PassesLowIndividualDegreeTest {params : Parameters} {d : ℕ}
    (strategy : ProjectiveStrategy params d) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

end ProjectiveStrategy

/-- A packaged family `x ↦ G^x` together with its witness operators and domination targets. -/
structure IndexedPolynomialFamily (params : Parameters) (d : ℕ) where
  meas : IndexedProjectiveSubMeasurement (Fq params) (Polynomial params) d
  witness : Fq params → Operator d := fun _ => default
  dominationTarget : Fq params → Polynomial params → Operator d := fun _ _ => default
  deriving Inhabited

namespace IndexedPolynomialFamily

/-- Placeholder averaged submeasurement `G = E_x G^x` from the paper. -/
def averagedSubMeasurement {params : Parameters} {d : ℕ}
    (_family : IndexedPolynomialFamily params d) : SubMeasurement (Polynomial params) d where
  name := s!"Gavg({params.m},{params.q},{params.d})"
  outcomeOperator := fun _ => { name := s!"Gavg({params.m},{params.q},{params.d}).outcome" }
  totalOperator := { name := s!"Gavg({params.m},{params.q},{params.d}).total" }

/-- Evaluate the slice family at a point `(u, x)` in `F_q^{m+1}`. -/
def evaluatedAtNextPoint {params : Parameters} {d : ℕ}
    (family : IndexedPolynomialFamily params d) :
    IndexedSubMeasurement (Point params.next) (Fq params) d :=
  fun u =>
    evaluateAt params (truncatePoint params u)
      ((family.meas (pointHeight params u)).toSubMeasurement)

structure Complete {params : Parameters} {d : ℕ} (family : IndexedPolynomialFamily params d)
    (ψ : QuantumState d) (kappa : Error) : Prop where
  averageCompleteness :
    CompletenessAtLeast ψ family.averagedSubMeasurement (1 - kappa)

structure ConsistentWithPoints {params : Parameters} {d : ℕ}
    (family : IndexedPolynomialFamily params d)
    (strategy : SymmetricStrategy params.next d) (zeta : Error) : Prop where
  pointConsistency :
    ConsistencyRel strategy.state (uniformDistribution (Point params.next))
      (IndexedProjectiveMeasurement.toIndexedSubMeasurement strategy.pointMeasurement)
      family.evaluatedAtNextPoint
      zeta

structure StronglySelfConsistent {params : Parameters} {d : ℕ}
    (family : IndexedPolynomialFamily params d)
    (ψ : QuantumState d) (zeta : Error) : Prop where
  sliceSelfConsistency :
    StrongSelfConsistencyRel ψ (uniformDistribution (Fq params))
      (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement family.meas)
      zeta

structure Bounded {params : Parameters} {d : ℕ}
    (family : IndexedPolynomialFamily params d)
    (ψ : QuantumState d) (zeta : Error) : Prop where
  slicePositiveSemidefinite : ∀ x, PositiveSemidefinite (family.witness x)
  sliceBoundedness :
    ∀ x, BoundedByOperator ψ ((family.meas x).toSubMeasurement) (family.witness x) zeta
  sliceDominatesTarget :
    ∀ x : Fq params, ∀ g : Polynomial params,
      DominatesOperator (family.witness x) (family.dominationTarget x g)

end IndexedPolynomialFamily

end MIPStarRE.LDT
