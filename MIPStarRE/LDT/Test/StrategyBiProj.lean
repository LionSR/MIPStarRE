import MIPStarRE.LDT.Test.StrategyCore

/-!
# Section 3 — Two-space projective strategies

Paper-faithful two-space projective strategy container `BiProjStrat params ιA ιB`
alongside the existing same-space `ProjStrat params ι` API. The paper's general
projective strategy (`test_definition.tex`, `def:general-projective-strategy`)
allows Alice and Bob to use different local Hilbert spaces, whereas the current
`ProjStrat` forces both provers onto a common local index type `ι`.

This module is the first low-risk step of the staged refactor outlined in
`docs/scouting/ch02_separate_local_spaces.md`:

* the two-space container does **not** carry `PermInvState` or `densityFixed`,
  since there is no canonical SWAP when `ιA ≠ ιB`;
* a forgetful embedding `ProjStrat.toBiProjStrat` reinterprets the current
  same-space strategy as the `ιA = ιB = ι` special case;
* the two-space branch-level failure probability mirrors the paper's
  low-individual-degree test without changing downstream same-space consumers;
* no downstream consumer (`SymStrat`, `StrategyFailures`, `MainTheorem`) is
  changed here — those migrations are tracked by later stages.

## References

* `references/ldt-paper/test_definition.tex`, `def:general-projective-strategy`
* `blueprint/src/chapter/ch02_test.tex`
* `docs/scouting/ch02_separate_local_spaces.md`
-/

namespace MIPStarRE.LDT

open scoped BigOperators

/-- Paper-faithful two-space projective strategy data.

This matches the paper's `def:general-projective-strategy`: Alice's and Bob's
measurements act on separate local carriers `ιA` and `ιB`, and the bipartite
state lives on `ιA × ιB` without a built-in swap symmetry.

The `isNormalized` field records that the bipartite state's density operator has
normalized trace `1`, mirroring `ProjStrat.isNormalized`.

No `permInvState` / `densityFixed` fields are carried: the SWAP reindexing used
by `PermInvState` is only defined on `ι × ι`, and there is no canonical swap
between distinct carriers. Paper-faithful symmetrization for heterogeneous local
spaces requires a genuine direct-sum construction (e.g. `Sum ιA ιB`) and is
deferred to a later stage of the refactor. -/
structure BiProjStrat (params : Parameters) [FieldModel params.q]
    (ιA : Type*) [Fintype ιA] [DecidableEq ιA]
    (ιB : Type*) [Fintype ιB] [DecidableEq ιB] where
  /-- Bipartite state on the tensor product of Alice's and Bob's local carriers. -/
  state : QuantumState (ιA × ιB)
  /-- The bipartite state's density operator is trace-normalized. -/
  isNormalized : state.IsNormalized
  /-- Alice's point-measurement family, acting on `ιA`. -/
  pointMeasurementA : IdxProjMeas (Point params) (Fq params) ιA
  /-- Alice's axis-parallel-line measurement family, acting on `ιA`. -/
  axisParallelMeasurementA : AxisParallelCovariantMeasurement params ιA
  /-- Alice's diagonal-line measurement family, acting on `ιA`. -/
  diagonalMeasurementA : DiagonalCovariantMeasurement params ιA
  /-- Bob's point-measurement family, acting on `ιB`. -/
  pointMeasurementB : IdxProjMeas (Point params) (Fq params) ιB
  /-- Bob's axis-parallel-line measurement family, acting on `ιB`. -/
  axisParallelMeasurementB : AxisParallelCovariantMeasurement params ιB
  /-- Bob's diagonal-line measurement family, acting on `ιB`. -/
  diagonalMeasurementB : DiagonalCovariantMeasurement params ιB

namespace BiProjStrat

variable {params : Parameters} [FieldModel params.q]
variable {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
variable {ιB : Type*} [Fintype ιB] [DecidableEq ιB]

/-! ### Paper test branches for two-space strategies -/

/-- Alice's point answers in the axis-parallel branch: Alice receives `u`,
the base point of the sampled line, and answers with `A^{A,u}`. -/
noncomputable def axisParallelPointAnswerFamilyA
    (strategy : BiProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιA :=
  fun s => (strategy.pointMeasurementA s.1).toSubMeas

/-- Bob's point answers in the axis-parallel branch: Bob receives `u`,
the base point of the sampled line, and answers with `A^{B,u}`. -/
noncomputable def axisParallelPointAnswerFamilyB
    (strategy : BiProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιB :=
  fun s => (strategy.pointMeasurementB s.1).toSubMeas

/-- Alice's axis-parallel-line answers: Alice receives `ℓ`, answers with
`B^{A,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def axisParallelLineAnswerFamilyA
    (strategy : BiProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιA :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurementA ℓ).toSubMeas)
      (· zeroCoord)

/-- Bob's axis-parallel-line answers: Bob receives `ℓ`, answers with
`B^{B,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def axisParallelLineAnswerFamilyB
    (strategy : BiProjStrat params ιA ιB) :
    IdxSubMeas (AxisParallelTestSample params) (Fq params) ιB :=
  fun s =>
    let ℓ : AxisParallelLine params :=
      { base := s.1, direction := s.2 }
    postprocess
      ((strategy.axisParallelMeasurementB ℓ).toSubMeas)
      (· zeroCoord)

/-- Alice's point answers in the restricted diagonal branch: Alice receives the
sampled base point `u` and answers with `A^{A,u}`. -/
noncomputable def diagonalPointAnswerFamilyA
    (strategy : BiProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιA :=
  fun s => (strategy.pointMeasurementA s.1).toSubMeas

/-- Bob's point answers in the restricted diagonal branch: Bob receives the
sampled base point `u` and answers with `A^{B,u}`. -/
noncomputable def diagonalPointAnswerFamilyB
    (strategy : BiProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιB :=
  fun s => (strategy.pointMeasurementB s.1).toSubMeas

/-- Alice's restricted diagonal-line answers: Alice receives `ℓ`, answers with
`L^{A,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def diagonalLineAnswerFamilyA
    (strategy : BiProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιA :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurementA ℓ).toSubMeas)
      (· zeroCoord)

/-- Bob's restricted diagonal-line answers: Bob receives `ℓ`, answers with
`L^{B,ℓ}`, and the verifier postprocesses to the value at the sampled base
point. -/
noncomputable def diagonalLineAnswerFamilyB
    (strategy : BiProjStrat params ιA ιB) (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ιB :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    let ℓ : DiagonalLine params :=
      { base := s.1, direction := v }
    postprocess
      ((strategy.diagonalMeasurementB ℓ).toSubMeas)
      (· zeroCoord)

/-- Axis-parallel branch component where Alice receives the sampled line and Bob
receives its base point. -/
noncomputable def axisParallelLineLeftPointRightFailureProbability
    (strategy : BiProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelLineAnswerFamilyA strategy)
    (axisParallelPointAnswerFamilyB strategy)

/-- Axis-parallel branch component where Alice receives the sampled base point
and Bob receives the sampled line. -/
noncomputable def axisParallelPointLeftLineRightFailureProbability
    (strategy : BiProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (AxisParallelTestSample params))
    (axisParallelPointAnswerFamilyA strategy)
    (axisParallelLineAnswerFamilyB strategy)

/-- The paper's axis-parallel branch for a two-space general strategy, averaged
over the two role choices. -/
noncomputable def axisParallelRoleAverage
    (strategy : BiProjStrat params ιA ιB) : Error :=
  (axisParallelLineLeftPointRightFailureProbability strategy +
    axisParallelPointLeftLineRightFailureProbability strategy) / 2

/-- Point-agreement branch: both provers receive the same point and the verifier
checks equality of their field answers. -/
noncomputable def pointAgreementFailureProbability
    (strategy : BiProjStrat params ιA ιB) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)

/-- Diagonal branch component where Alice receives the sampled diagonal line and
Bob receives its base point. -/
noncomputable def diagonalLineLeftPointRightFailureProbability
    (strategy : BiProjStrat params ιA ιB) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalLineAnswerFamilyA strategy j)
        (diagonalPointAnswerFamilyB strategy j)

/-- Diagonal branch component where Alice receives the sampled base point and
Bob receives the sampled diagonal line. -/
noncomputable def diagonalPointLeftLineRightFailureProbability
    (strategy : BiProjStrat params ιA ιB) : Error :=
  (1 / (params.m : Error)) *
    ∑ j : Fin params.m,
      bipartiteConsError strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (diagonalPointAnswerFamilyA strategy j)
        (diagonalLineAnswerFamilyB strategy j)

/-- The paper's diagonal branch for a two-space general strategy, averaged over
the two role choices and the restricted diagonal samples. -/
noncomputable def diagonalRoleAverage
    (strategy : BiProjStrat params ιA ιB) : Error :=
  (diagonalLineLeftPointRightFailureProbability strategy +
    diagonalPointLeftLineRightFailureProbability strategy) / 2

/-- Trace-based failure surrogate for the full low-individual-degree test for a
paper-faithful two-space projective strategy.

This is the heterogeneous analogue of
`ProjStrat.lowIndividualDegreeFailureProbability`: axis-parallel consistency,
point agreement, and diagonal consistency are averaged
with weights `1 / 3`, while the line branches are themselves averaged over the
two role choices. -/
noncomputable def lowIndividualDegreeFailureProbability
    (strategy : BiProjStrat params ιA ιB) : Error :=
  (strategy.axisParallelRoleAverage + strategy.pointAgreementFailureProbability +
    strategy.diagonalRoleAverage) / 3

/-- Passing the full low-individual-degree test with error `ε`, for the
paper-faithful two-space strategy container. -/
structure PassesLowIndividualDegreeTest
    (strategy : BiProjStrat params ιA ιB) (eps : Error) : Prop where
  soundnessHypothesis : strategy.lowIndividualDegreeFailureProbability ≤ eps

end BiProjStrat

namespace ProjStrat

/-- Forgetful embedding of the same-space `ProjStrat params ι` into the
paper-faithful two-space container `BiProjStrat params ι ι`.

Discards the swap-symmetry data (`permInvState`, `densityFixed`) since
`BiProjStrat` does not carry same-space swap assumptions by design. -/
def toBiProjStrat {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) : BiProjStrat params ι ι where
  state := strategy.state
  isNormalized := strategy.isNormalized
  pointMeasurementA := strategy.pointMeasurementA
  axisParallelMeasurementA := strategy.axisParallelMeasurementA
  diagonalMeasurementA := strategy.diagonalMeasurementA
  pointMeasurementB := strategy.pointMeasurementB
  axisParallelMeasurementB := strategy.axisParallelMeasurementB
  diagonalMeasurementB := strategy.diagonalMeasurementB

end ProjStrat

end MIPStarRE.LDT
