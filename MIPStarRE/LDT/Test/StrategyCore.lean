import MIPStarRE.LDT.Test.Defs

/-!
# Section 3 — Strategy core

Base state-invariance and strategy structures for the low individual degree test.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

instance : Fintype Role where
  elems := {Role.A, Role.B}
  complete r := by
    cases r <;> simp

/-- The SWAP reindexing on `ι × ι`: permutes the two tensor factors.
`swapDensity M (i₁,i₂) (j₁,j₂) = M (i₂,i₁) (j₂,j₁)`. -/
def swapDensity {ι : Type*} (M : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  Matrix.of fun (ij : ι × ι) (kl : ι × ι) => M (ij.2, ij.1) (kl.2, kl.1)

/-- Permutation-invariance for a bipartite state on `ι × ι`.

The primary datum is that the density operator is fixed by the SWAP reindexing,
`swapDensity ψ.density = ψ.density`.  We also cache the frequently used
one-sided expectation consequence
`ev ψ (leftTensor M) = ev ψ (rightTensor M)`.
This matches the symmetric-strategy construction used in the paper
(Section 3) and exposes enough symmetry to swap fully bipartite
consistency expressions. -/
structure PermInvState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) : Prop where
  /-- The density operator is fixed by the SWAP reindexing. -/
  density_swap : swapDensity ψ.density = ψ.density
  /-- Swapping tensor factors preserves one-sided expectation values. -/
  swap_ev : ∀ (M : MIPStarRE.Quantum.Op ι),
    ev ψ (leftTensor (ι₂ := ι) M) =
      ev ψ (rightTensor (ι₁ := ι) M)

/-- Reparametrization invariance for diagonal-line measurements: evaluating a
rebased line at `zeroCoord` agrees outcome-wise with evaluating the original
line at the rebasing parameter.

At the answer level, the geometric identity is
`DiagonalLinePolynomial.reparamAt_apply_zero`. This predicate is stronger: it
asserts that the *measurement family itself* is covariant under rebasing the
question index. -/
def DiagonalEvaluationReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t a : Fq params),
    (postprocess ((M (DiagonalLine.rebaseAt ℓ t)).toSubMeas) (· zeroCoord)).outcome a =
      (postprocess ((M ℓ).toSubMeas) (fun f => f t)).outcome a

/-- Reparametrization invariance for axis-parallel-line measurements: evaluating a
rebased line at `zeroCoord` agrees outcome-wise with evaluating the original
line at the rebasing parameter. -/
def AxisParallelEvaluationReparamInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t a : Fq params),
    (postprocess ((M (AxisParallelLine.rebaseAt ℓ t)).toSubMeas) (· zeroCoord)).outcome a =
      (postprocess ((M ℓ).toSubMeas) (fun f => f t)).outcome a

namespace AxisParallelLine

/-- Transport an axis-parallel-line measurement along rebasing of the line
question by translating its polynomial outcomes. -/
noncomputable def transportMeasurement {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ProjMeas (AxisLinePolynomial params) ι) (t : Fq params) :
    ProjMeas (AxisLinePolynomial params) ι :=
  ProjMeas.transport (AxisLinePolynomial.reparamAtEquiv (params := params) t) M

/-- Evaluating a transported axis-line measurement at `zeroCoord` agrees with
reading the original measurement at the rebasing parameter. -/
theorem transportMeasurement_postprocess_zero
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ProjMeas (AxisLinePolynomial params) ι) (t a : Fq params) :
    (postprocess (transportMeasurement (params := params) M t).toSubMeas
        (· zeroCoord)).outcome a =
      (postprocess M.toSubMeas (fun f => f t)).outcome a := by
  have h :=
    SubMeas.postprocess_transport
      (e := AxisLinePolynomial.reparamAtEquiv (params := params) t)
      (A := M.toSubMeas)
      (f := fun g : AxisLinePolynomial params => g zeroCoord)
  simpa [transportMeasurement, AxisLinePolynomial.reparamAtEquiv,
    AxisLinePolynomial.reparamAt_apply_zero, addCoord, zeroCoord] using
    congrArg (fun A => A.outcome a) h

end AxisParallelLine

namespace DiagonalLine

/-- Transport a diagonal-line measurement along rebasing of the line question by
translating its polynomial outcomes. -/
noncomputable def transportMeasurement {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ProjMeas (DiagonalLinePolynomial params) ι) (t : Fq params) :
    ProjMeas (DiagonalLinePolynomial params) ι :=
  ProjMeas.transport (DiagonalLinePolynomial.reparamAtEquiv (params := params) t) M

/-- Evaluating a transported diagonal-line measurement at `zeroCoord` agrees with
reading the original measurement at the rebasing parameter. -/
theorem transportMeasurement_postprocess_zero
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ProjMeas (DiagonalLinePolynomial params) ι) (t a : Fq params) :
    (postprocess (transportMeasurement (params := params) M t).toSubMeas
        (· zeroCoord)).outcome a =
      (postprocess M.toSubMeas (fun f => f t)).outcome a := by
  have h :=
    SubMeas.postprocess_transport
      (e := DiagonalLinePolynomial.reparamAtEquiv (params := params) t)
      (A := M.toSubMeas)
      (f := fun g : DiagonalLinePolynomial params => g zeroCoord)
  simpa [transportMeasurement, DiagonalLinePolynomial.reparamAtEquiv,
    DiagonalLinePolynomial.reparamAt_apply_zero, addCoord, zeroCoord] using
    congrArg (fun A => A.outcome a) h

end DiagonalLine

/-- Stronger rebasing compatibility for axis-parallel-line measurements: the
measurement indexed by the rebased line is equal to the transport of the
original measurement along the answer reparametrization equivalence. -/
def AxisParallelMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : AxisParallelLine params) (t : Fq params),
    M (AxisParallelLine.rebaseAt ℓ t) =
      AxisParallelLine.transportMeasurement (params := params) (M ℓ) t

/-- Stronger rebasing compatibility for diagonal-line measurements: the
measurement indexed by the rebased line is equal to the transport of the
original measurement along the answer reparametrization equivalence. -/
def DiagonalMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t : Fq params),
    M (DiagonalLine.rebaseAt ℓ t) =
      DiagonalLine.transportMeasurement (params := params) (M ℓ) t

/-- The stronger transport-level axis-parallel compatibility implies the older
outcome-level reparametrization invariant predicate. -/
theorem AxisParallelMeasurementTransportInvariant.toEvaluationReparamInvariant
    {params : Parameters} [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι}
    (hM : AxisParallelMeasurementTransportInvariant params M) :
    AxisParallelEvaluationReparamInvariant params M := by
  intro ℓ t a
  rw [hM ℓ t]
  exact AxisParallelLine.transportMeasurement_postprocess_zero
    (params := params) (M := M ℓ) t a

/-- The stronger transport-level diagonal compatibility implies the older
outcome-level reparametrization invariant predicate. -/
theorem DiagonalMeasurementTransportInvariant.toEvaluationReparamInvariant
    {params : Parameters} [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι}
    (hM : DiagonalMeasurementTransportInvariant params M) :
    DiagonalEvaluationReparamInvariant params M := by
  intro ℓ t a
  rw [hM ℓ t]
  exact DiagonalLine.transportMeasurement_postprocess_zero
    (params := params) (M := M ℓ) t a

/-- Axis-parallel line measurements bundled with the stronger transport-level
rebasing covariance. -/
structure AxisParallelCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  toIdxProjMeas :
    IdxProjMeas (AxisParallelLine params) (AxisLinePolynomial params) ι
  transportInvariant :
    AxisParallelMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    CoeFun (AxisParallelCovariantMeasurement params ι)
      (fun _ => AxisParallelLine params → ProjMeas (AxisLinePolynomial params) ι) where
  coe M := M.toIdxProjMeas

namespace AxisParallelCovariantMeasurement

/-- A covariant wrapper automatically satisfies the older evaluation-level
rebasing invariant. -/
theorem reparamInvariant {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : AxisParallelCovariantMeasurement params ι) :
    AxisParallelEvaluationReparamInvariant params M.toIdxProjMeas :=
  M.transportInvariant.toEvaluationReparamInvariant

end AxisParallelCovariantMeasurement

/-- Diagonal line measurements bundled with the stronger transport-level
rebasing covariance. -/
structure DiagonalCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  toIdxProjMeas :
    IdxProjMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι
  transportInvariant :
    DiagonalMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    CoeFun (DiagonalCovariantMeasurement params ι)
      (fun _ => DiagonalLine params → ProjMeas (DiagonalLinePolynomial params) ι) where
  coe M := M.toIdxProjMeas

namespace DiagonalCovariantMeasurement

/-- A covariant wrapper automatically satisfies the older evaluation-level
rebasing invariant. -/
theorem reparamInvariant {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : DiagonalCovariantMeasurement params ι) :
    DiagonalEvaluationReparamInvariant params M.toIdxProjMeas :=
  M.transportInvariant.toEvaluationReparamInvariant

end DiagonalCovariantMeasurement

/-- Transport covariance for diagonal-line measurements whose answers are the
paper-level line functions. -/
def DiagonalAnswerMeasurementTransportInvariant (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) ι) : Prop :=
  ∀ (ℓ : DiagonalLine params) (t : Fq params),
    M (DiagonalLine.rebaseAt ℓ t) =
      ProjMeas.transport (DiagonalLineAnswer.reparamAtEquiv t) (M ℓ)

/-- Diagonal-line measurements with paper-level function answers, bundled with
transport-level rebasing covariance.

This parallel API is intended for the paper-faithful restriction redesign: unlike
`DiagonalLinePolynomial`, the function-answer alphabet admits a total slice
append/restrict equivalence. -/
structure DiagonalAnswerCovariantMeasurement (params : Parameters)
    [FieldModel params.q] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  toIdxProjMeas :
    IdxProjMeas (DiagonalLine params) (DiagonalLineAnswer params) ι
  transportInvariant :
    DiagonalAnswerMeasurementTransportInvariant params toIdxProjMeas

instance {params : Parameters} [FieldModel params.q] {ι : Type*}
    [Fintype ι] [DecidableEq ι] :
    CoeFun (DiagonalAnswerCovariantMeasurement params ι)
      (fun _ => DiagonalLine params → ProjMeas (DiagonalLineAnswer params) ι) where
  coe M := M.toIdxProjMeas

/-- Paper-level symmetric strategy data whose diagonal-line answers are functions.

This parallel structure is the target shape for the restriction redesign in
Section 6: restricting an ambient diagonal line to a slice is total for function
answers, unlike the current degree-bounded `DiagonalLinePolynomial` alphabet. -/
structure AnswerSymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)
  permInvState : PermInvState state
  densityFixed : swapDensity state.density = state.density
  isNormalized : state.IsNormalized
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurement : AxisParallelCovariantMeasurement params ι
  diagonalMeasurement : DiagonalAnswerCovariantMeasurement params ι

/-- Paper-local symmetric strategy data.

The line-measurement fields are bundled as transport-covariant wrappers:
rebasing the question index is required to agree with transporting the
projective measurement along the corresponding answer reparametrization
equivalence. This is stronger than the older evaluation-level formulas
at `zeroCoord`, but those formulas remain available as derived lemmas via
`AxisParallelCovariantMeasurement.reparamInvariant` and
`DiagonalCovariantMeasurement.reparamInvariant`.

The `isNormalized` field records that the bipartite state's density
operator has normalized trace `1`. For pure states, this coincides
with the usual unit-vector condition (`⟨ψ|ψ⟩ = 1`) used in the paper.
Bundling normalization with the strategy avoids threading a
`state.IsNormalized` hypothesis through every downstream consumer
(pasting cascade, `triangleSub` users, self-improvement helpers). -/
structure SymStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)  -- bipartite state on ℋ ⊗ ℋ
  permInvState : PermInvState state
  densityFixed : swapDensity state.density = state.density
  isNormalized : state.IsNormalized
  pointMeasurement : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurement : AxisParallelCovariantMeasurement params ι
  diagonalMeasurement : DiagonalCovariantMeasurement params ι

-- NOTE: no global `Inhabited` instance for `SymStrat`; constructing default
-- projective measurement families is non-canonical and requires additional
-- assumptions on outcome types.

/-- Encoded samples `(u, i)` for the axis-parallel lines test.
The paper samples a random point `u ∈ F_q^m` and a coordinate
`i ∈ {1, …, m}`. In Lean, `Fin params.m` represents the 0-indexed
coordinates `{0, …, m - 1}`, corresponding to the paper's 1-indexed
choice. The sample forms the axis-parallel line through `u` in that
coordinate direction. -/
abbrev AxisParallelTestSample (params : Parameters) :=
  Point params × Fin params.m

/-- Extend restricted direction coordinates to a full direction vector.
For restriction index `j` (0-indexed), the first `j + 1` coordinates
are the given free coordinates and the remaining are zero.
This matches the paper's convention that `v` has its last `m − i`
coordinates zero, where `i = j + 1`. -/
def extendRestrictedDirection {params : Parameters}
    [FieldModel params.q] (j : Fin params.m)
    (freeCoords : Fin (j.val + 1) → Fq params) :
    Point params :=
  fun k =>
    if h : k.val ≤ j.val then
      freeCoords ⟨k.val, Nat.lt_succ_of_le h⟩
    else zeroCoord

/-- Encoded samples `(u, freeCoords)` for the `j`-restricted diagonal
lines test. The base point `u ∈ F_q^m` and the free coordinates of
the restricted direction (first `j + 1` coordinates; rest are zero).
The full diagonal test averages over `j ∈ {0, …, m − 1}`. -/
abbrev RestrictedDiagonalSample (params : Parameters)
    (j : Fin params.m) :=
  Point params × (Fin (j.val + 1) → Fq params)

/-- The restricted diagonal sample space is nonempty. -/
instance restrictedDiagonalSampleNonempty (params : Parameters) (j : Fin params.m) :
    Nonempty (RestrictedDiagonalSample params j) :=
  inferInstance

/-- Sampled point answers in the axis-parallel lines test.
The point player receives `u` (the base point) and answers with
their measurement at `u`. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  fun s => (strategy.pointMeasurement s.1).toSubMeas

/-- Sampled line answers in the axis-parallel lines test,
evaluated at the base point `u`.
The line player receives `ℓ` and returns a polynomial `f`.
The verifier checks `f(u) = a`; since `u = ℓ.pointAt zeroCoord`,
we evaluate `f` at `zeroCoord`. -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params)
      (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurement ℓ).toSubMeas)
      (· zeroCoord)

-- Paper: `not:conditioned-on-last-direction` abbreviates the axis-parallel
-- line in the last coordinate direction of `F_q^(m+1)` by its base point `u`.
/-- The axis-parallel line in `F_q^(m+1)` through `(u, 0)` in the last
coordinate direction. This is the geometric line denoted `B^u` in the paper's
last-direction notation. -/
def lastDirectionLine (params : Parameters) [FieldModel params.q]
    (u : Point params) : AxisParallelLine params.next where
  base := appendPoint params u zeroCoord
  direction := lastCoord params

-- Paper: `not:conditioned-on-last-direction` writes `B^u` for the axis-parallel
-- line measurement conditioned on the last direction choice.
/-- The axis-parallel line measurement family restricted to the paper's
last-direction notation `u ↦ B^u`. -/
noncomputable def lastDirectionMeasurementFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι) :
    IdxProjMeas (Point params) (AxisLinePolynomial params.next) ι :=
  fun u => strategy.axisParallelMeasurement (lastDirectionLine params u)

/-- Sampled point answers in the `j`-restricted diagonal test.
The point player receives `u` and answers at `u`. -/
noncomputable def diagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  fun s => (strategy.pointMeasurement s.1).toSubMeas

/-- Sampled diagonal-line answers in the `j`-restricted diagonal
test, evaluated at the base point `u`.
Since `u = ℓ.pointAt zeroCoord`, we evaluate `f` at
`zeroCoord`. -/
noncomputable def diagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j)
      (Fq params) ι :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurement ℓ).toSubMeas)
      (· zeroCoord)

namespace AnswerSymStrat

/-- Sampled point answers in the axis-parallel lines test for an answer-valued
symmetric strategy. -/
noncomputable def axisParallelPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s => (strategy.pointMeasurement s.1).toSubMeas

/-- Sampled line answers in the axis-parallel lines test for an answer-valued
symmetric strategy, evaluated at the base point. -/
noncomputable def axisParallelLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ι :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurement ℓ).toSubMeas)
      (· zeroCoord)

/-- Sampled point answers in the restricted diagonal test for an answer-valued
symmetric strategy. -/
noncomputable def diagonalPointAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  fun s => (strategy.pointMeasurement s.1).toSubMeas

/-- Sampled diagonal-line answers in the restricted diagonal test for an
answer-valued symmetric strategy, evaluated at the base point. -/
noncomputable def diagonalLineAnswerFamily
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurement ℓ).toSubMeas)
      (· zeroCoord)

/-- Axis-parallel failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def axisParallelFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamily strategy)
    (axisParallelLineAnswerFamily strategy)

/-- Self-consistency failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def selfConsistencyFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) : Error :=
  bipartiteSSCError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)

/-- Diagonal-line failure surrogate for an answer-valued symmetric strategy. -/
noncomputable def diagonalFailureProbability
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : AnswerSymStrat params ι) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamily strategy j)
        (diagonalLineAnswerFamily strategy j)

/-- Goodness data for an answer-valued symmetric strategy. -/
structure IsGood {params : Parameters}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [FieldModel params.q]
    (strategy : AnswerSymStrat params ι)
    (eps delta gamma : Error) : Prop where
  /-- The axis-parallel test fails with probability at most `eps`. -/
  axisParallelTest : strategy.axisParallelFailureProbability ≤ eps
  /-- The self-consistency test fails with probability at most `delta`. -/
  selfConsistencyTest : strategy.selfConsistencyFailureProbability ≤ delta
  /-- The diagonal-line test fails with probability at most `gamma`. -/
  diagonalLineTest : strategy.diagonalFailureProbability ≤ gamma

end AnswerSymStrat

/-- Paper-local (not necessarily symmetric) projective strategy data.

Carries `isNormalized` so that symmetrization constructors
(`leftAsSymmetric`, `rightAsSymmetric`, `classicalRoleSymmStrategy`)
can discharge the matching `SymStrat.isNormalized` field without
threading an extra hypothesis. -/
structure ProjStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)  -- bipartite state on ℋ ⊗ ℋ
  permInvState : PermInvState state
  densityFixed : swapDensity state.density = state.density
  isNormalized : state.IsNormalized
  pointMeasurementA : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurementA : AxisParallelCovariantMeasurement params ι
  diagonalMeasurementA : DiagonalCovariantMeasurement params ι
  pointMeasurementB : IdxProjMeas (Point params) (Fq params) ι
  axisParallelMeasurementB : AxisParallelCovariantMeasurement params ι
  diagonalMeasurementB : DiagonalCovariantMeasurement params ι


end MIPStarRE.LDT
