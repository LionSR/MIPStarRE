import MIPStarRE.LDT.Test.Defs

/-!
# Section 3 — Strategy

Symmetric and projective strategy structures for the low individual degree test,
together with the test-passing and consistency predicates.

All operator fields now use `Op ι` directly with a generic `Fintype` index `ι`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

noncomputable section

namespace MIPStarRE.LDT

/-- Invariance predicate for the symmetric shared state. -/
structure PermInvState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (_ψ : QuantumState ι) : Prop where
  placeholder : True

/-- Paper-local symmetric strategy data. -/
structure SymStrat (params : Parameters) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState ι
  statePermutationInvariant : PermInvState state := ⟨trivial⟩
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurement :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  diagonalMeasurement :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι

instance {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Inhabited (SymStrat params ι) where
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
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeas

/-- Sampled line answers, evaluated at the sampled parameter, in the axis-parallel lines test. -/
noncomputable def axisParallelLineAnswerFamily {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeas) (fun g => g s.2.2)

/-- Sampled point answers in the diagonal lines test. -/
noncomputable def diagonalPointAnswerFamily {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (DiagonalTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeas

/-- Sampled diagonal-line answers, evaluated at the sampled parameter. -/
noncomputable def diagonalLineAnswerFamily {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (DiagonalTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.diagonalMeasurement ℓ).toSubMeas) (fun g => g s.2.2)

/-- Paper-local (not necessarily symmetric) projective strategy data. -/
structure ProjStrat (params : Parameters) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState ι
  pointMeasurementA : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurementA :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  diagonalMeasurementA :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι
  pointMeasurementB : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurementB :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  diagonalMeasurementB :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι
  deriving Inhabited

namespace SymStrat

/-- Trace-based failure surrogate for the axis-parallel lines test. -/
noncomputable def axisParallelFailureProbability {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  consError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Trace-based failure surrogate for the self-consistency test. -/
noncomputable def selfConsistencyFailureProbability {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  sscError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Trace-based failure surrogate for the diagonal lines test. -/
noncomputable def diagonalFailureProbability {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  consError strategy.state
    (uniformDistribution (DiagonalTestSample params))
    (diagonalPointAnswerFamily strategy)
    (diagonalLineAnswerFamily strategy)

/-- The paper's notion of an `(ε,δ,γ)`-good symmetric strategy. -/
structure IsGood {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error) : Prop where
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end SymStrat

namespace ProjStrat

/-- View the left prover's local data as a symmetric-strategy-style package. -/
def leftAsSymmetric {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  pointMeasurement := strategy.pointMeasurementA
  axisParallelMeasurement := strategy.axisParallelMeasurementA
  diagonalMeasurement := strategy.diagonalMeasurementA

/-- View the right prover's local data as a symmetric-strategy-style package. -/
def rightAsSymmetric {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  pointMeasurement := strategy.pointMeasurementB
  axisParallelMeasurement := strategy.axisParallelMeasurementB
  diagonalMeasurement := strategy.diagonalMeasurementB

/-- Trace-based failure surrogate for the full low-individual-degree test. -/
noncomputable def lowIndividualDegreeFailureProbability {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  let pointAgreement :=
    consError strategy.state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
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
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

end ProjStrat

/-- A packaged family `x ↦ G^x` together with its witness operators and domination targets. -/
structure IdxPolyFamily (params : Parameters) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  meas : IdxProjSubMeas (Fq params) (Polynomial params) ι
  witness : Fq params → MIPStarRE.Quantum.Op ι := fun _ => 0
  dominationTarget : Fq params → Polynomial params → MIPStarRE.Quantum.Op ι := fun _ _ => 0
  deriving Inhabited

namespace IdxPolyFamily

/-- Placeholder averaged submeasurement `G = E_x G^x` from the paper. -/
def averagedSubMeas {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (_family : IdxPolyFamily params ι) : SubMeas (Polynomial params) ι where
  outcome := fun _ => 0
  total := 0

/-- Evaluate the slice family at a point `(u, x)` in `F_q^{m+1}`. -/
def evaluatedAtNextPoint {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    evaluateAt params (truncatePoint params u)
      ((family.meas (pointHeight params u)).toSubMeas)

structure Complete {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState ι) (kappa : Error) : Prop where
  averageCompleteness :
    CompletenessAtLeast ψ family.averagedSubMeas (1 - kappa)

structure ConsistentWithPoints {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (strategy : SymStrat params.next ι) (zeta : Error) : Prop where
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint
      zeta

structure StronglySelfConsistent {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState ι) (zeta : Error) : Prop where
  sliceSelfConsistency :
    SSCRel ψ (uniformDistribution (Fq params))
      (IdxProjSubMeas.toIdxSubMeas family.meas)
      zeta

structure Bounded {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState ι) (zeta : Error) : Prop where
  sliceOpPSD : ∀ x, 0 ≤ family.witness x
  sliceBoundedness :
    ∀ x, BoundedByOperator ψ ((family.meas x).toSubMeas) (family.witness x) zeta
  sliceDominatesTarget :
    ∀ x : Fq params, ∀ g : Polynomial params,
      0 ≤ family.witness x - family.dominationTarget x g

end IdxPolyFamily

end MIPStarRE.LDT
