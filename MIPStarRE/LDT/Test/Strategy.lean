import MIPStarRE.LDT.Test.Defs

/-!
# Section 3 — Strategy

Symmetric and projective strategy structures for the low individual degree test,
together with the test-passing and consistency predicates.

All operator fields now use `Op ι` directly with a generic `Fintype` index `ι`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- The SWAP reindexing on `ι × ι`: permutes the two tensor factors.
`swapDensity M (i₁,i₂) (j₁,j₂) = M (i₂,i₁) (j₂,j₁)`. -/
def swapDensity {ι : Type*} (M : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  Matrix.of fun (ij : ι × ι) (kl : ι × ι) => M (ij.2, ij.1) (kl.2, kl.1)

/-- Permutation-invariance for a bipartite state on `ι × ι`.

The key property (`swap_ev`) is that expectation values are symmetric
under swapping the two tensor factors:
  `ev ψ (leftTensor M) = ev ψ (rightTensor M)`.
This is the formal content of "ψ is permutation-invariant" in the paper
(see Section 3).

For concrete strategies, this should be discharged via
`ψ.density = swapDensity ψ.density`. -/
structure PermInvState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) : Prop where
  /-- Swapping tensor factors preserves expectation values. -/
  swap_ev : ∀ (M : MIPStarRE.Quantum.Op ι),
    ev ψ (leftTensor (ι₂ := ι) M) =
      ev ψ (rightTensor (ι₁ := ι) M)

/-- Paper-local symmetric strategy data. -/
structure SymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)  -- bipartite state on ℋ ⊗ ℋ
  permInvState : PermInvState state
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurement :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  diagonalMeasurement :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι

-- NOTE: no global `Inhabited` instance for `SymStrat`; constructing default
-- projective measurement families is non-canonical and requires additional
-- assumptions on outcome types.

/-- Encoded samples `(u₀, i, t)` for the axis-parallel lines test. -/
abbrev AxisParallelTestSample (params : Parameters) := Point params × (Fin params.m × Fq params)

/-- Encoded samples `(u₀, v, t)` for the diagonal lines test. -/
abbrev DiagonalTestSample (params : Parameters) := Point params × (Point params × Fq params)

/-- Sampled point answers in the axis-parallel lines test. -/
noncomputable def axisParallelPointAnswerFamily {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeas

/-- Sampled line answers, evaluated at the sampled parameter, in the axis-parallel lines test. -/
noncomputable def axisParallelLineAnswerFamily {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.axisParallelMeasurement ℓ).toSubMeas) (fun g => g s.2.2)

/-- Sampled point answers in the diagonal lines test. -/
noncomputable def diagonalPointAnswerFamily {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (DiagonalTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    (strategy.pointMeasurement (ℓ.pointAt s.2.2)).toSubMeas

/-- Sampled diagonal-line answers, evaluated at the sampled parameter. -/
noncomputable def diagonalLineAnswerFamily {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (DiagonalTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : DiagonalLine params := { base := s.1, direction := s.2.1 }
    postprocess ((strategy.diagonalMeasurement ℓ).toSubMeas) (fun g => g s.2.2)

/-- Paper-local (not necessarily symmetric) projective strategy data. -/
structure ProjStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)  -- bipartite state on ℋ ⊗ ℋ
  permInvState : PermInvState state
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

namespace SymStrat

/-- Trace-based failure surrogate for the axis-parallel lines test.
Alice's point answers act on the left register, and Bob's line answers
act on the right register of the bipartite state. -/
noncomputable def axisParallelFailureProbability {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Trace-based failure surrogate for the self-consistency test.
Uses the bipartite SSC defect (cross-register overlap `∑ ev(A ⊗ A)`),
matching `def:strong-self-consistency` in `preliminaries.tex`. -/
noncomputable def selfConsistencyFailureProbability {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Trace-based failure surrogate for the diagonal lines test.
Alice's point answers act on the left register, and Bob's diagonal-line
answers act on the right register of the bipartite state. -/
noncomputable def diagonalFailureProbability {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (DiagonalTestSample params))
    (diagonalPointAnswerFamily strategy)
    (diagonalLineAnswerFamily strategy)

/-- The paper's notion of an `(ε,δ,γ)`-good symmetric strategy. -/
structure IsGood {params : Parameters} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error) : Prop where
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end SymStrat

namespace ProjStrat

/-- View the left prover's local data as a symmetric-strategy-style package. -/
def leftAsSymmetric {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  pointMeasurement := strategy.pointMeasurementA
  axisParallelMeasurement := strategy.axisParallelMeasurementA
  diagonalMeasurement := strategy.diagonalMeasurementA

/-- View the right prover's local data as a symmetric-strategy-style package. -/
def rightAsSymmetric {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) :
    SymStrat params ι where
  state := strategy.state
  permInvState := strategy.permInvState
  pointMeasurement := strategy.pointMeasurementB
  axisParallelMeasurement := strategy.axisParallelMeasurementB
  diagonalMeasurement := strategy.diagonalMeasurementB

/-- Trace-based failure surrogate for the full low-individual-degree test. -/
noncomputable def lowIndividualDegreeFailureProbability {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : Error :=
  let left := strategy.leftAsSymmetric
  let right := strategy.rightAsSymmetric
  let pointAgreement :=
    bipartiteConsError strategy.state
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
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

end ProjStrat

/-- A packaged family `x ↦ G^x` together with its witness operators and domination targets. -/
structure IdxPolyFamily (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  meas : IdxProjSubMeas (Fq params) (Polynomial params) ι
  witness : Fq params → MIPStarRE.Quantum.Op ι := fun _ => 0
  dominationTarget : Fq params → Polynomial params → MIPStarRE.Quantum.Op ι := fun _ _ => 0
  deriving Inhabited

namespace IdxPolyFamily

/-- The averaged submeasurement `G = E_x G^x`: average the slice
measurements over the uniform distribution on slice heights `x ∈ F_q`. -/
noncomputable def averagedSubMeas {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι) :
    SubMeas (Polynomial params) ι where
  outcome := fun g =>
    let 𝒟 := uniformDistribution (Fq params)
    ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.outcome g
  total :=
    let 𝒟 := uniformDistribution (Fq params)
    ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.total
  outcome_pos := by
    intro g
    let 𝒟 := uniformDistribution (Fq params)
    exact Finset.sum_nonneg fun x _ =>
      smul_nonneg (𝒟.nonnegative x) ((family.meas x).outcome_pos g)
  sum_eq_total := by
    classical
    let 𝒟 := uniformDistribution (Fq params)
    calc
      ∑ g, ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.outcome g
          = ∑ x ∈ 𝒟.support, ∑ g, 𝒟.weight x • (family.meas x).toSubMeas.outcome g := by
              rw [Finset.sum_comm]
      _ = ∑ x ∈ 𝒟.support, 𝒟.weight x • ∑ g, (family.meas x).toSubMeas.outcome g := by
            apply Finset.sum_congr rfl
            intro x _
            rw [← Finset.smul_sum]
      _ = ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.total := by
            apply Finset.sum_congr rfl
            intro x _
            rw [(family.meas x).toSubMeas.sum_eq_total]
  total_le_one := by
    let 𝒟 := uniformDistribution (Fq params)
    calc
      ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.total
        ≤ ∑ x ∈ 𝒟.support, 𝒟.weight x • (1 : MIPStarRE.Quantum.Op ι) := by
            exact Finset.sum_le_sum fun x _ =>
              smul_le_smul_of_nonneg_left (family.meas x).toSubMeas.total_le_one (𝒟.nonnegative x)
      _ = (∑ x ∈ 𝒟.support, 𝒟.weight x) • (1 : MIPStarRE.Quantum.Op ι) := by
            rw [Finset.sum_smul]
      _ ≤ (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
            exact smul_le_smul_of_nonneg_right
              (uniformDistribution_weight_sum_le_one (Fq params)) zero_le_one
      _ = 1 := by simp

/-- Evaluate the slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluatedAtNextPoint {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    evaluateAt params (truncatePoint params u)
      ((family.meas (pointHeight params u)).toSubMeas)

/-- Weighted sum of operators over a distribution's finite support. -/
private noncomputable def averageOperatorOverDistribution' {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op ι :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a • f a

/-- Averaged point operator `E_u A^u_{h(u)}` appearing in source-style
boundedness assumptions. -/
noncomputable def averagedPointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) (h : Polynomial params) :
    MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution' (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement u).toSubMeas.outcome (h u))

/-- Slice-wise averaged point operator `E_u A^{u,x}_{g(u)}` from the paper's
boundedness hypothesis. -/
noncomputable def averagedSlicePointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution' (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))

structure Complete {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (kappa : Error) : Prop where
  averageCompleteness :
    CompletenessAtLeast ψ family.averagedSubMeas.liftLeft (1 - kappa)

structure ConsistentWithPoints {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (strategy : SymStrat params.next ι) (zeta : Error) : Prop where
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint
      zeta

structure StronglySelfConsistent {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (zeta : Error) : Prop where
  sliceSelfConsistency :
    SDDRel ψ (uniformDistribution (Fq params))
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas))
      zeta

structure Bounded {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (zeta : Error) : Prop where
  sliceOpPSD : ∀ x, 0 ≤ family.witness x
  sliceBoundedness :
    avgOver (uniformDistribution (Fq params))
      (fun x =>
        ev ψ <|
          leftTensor (ι₂ := ι) (family.witness x) *
            rightTensor (ι₁ := ι) (1 - (family.meas x).toSubMeas.total)) ≤ zeta
  sliceDominatesTarget :
    ∀ x : Fq params, ∀ g : Polynomial params,
      0 ≤ family.witness x - family.dominationTarget x g

/-- Paper-faithful boundedness input for slice-indexed polynomial families.

This extends `IdxPolyFamily.Bounded` with the missing source-side identification
between the abstract domination target and the averaged point operator
`E_u A^{u,x}_{g(u)}`. -/
structure SliceBoundednessInput {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  bounded : family.Bounded strategy.state zeta
  dominationTargetAgrees :
    ∀ x : Fq params, ∀ g : Polynomial params,
      family.dominationTarget x g =
        averagedSlicePointEvaluationOperator strategy x g

end IdxPolyFamily

end MIPStarRE.LDT
