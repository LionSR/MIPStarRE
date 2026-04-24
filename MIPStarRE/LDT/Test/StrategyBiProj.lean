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
* no downstream consumer (`SymStrat`, `StrategyFailures`, `MainTheorem`) is
  changed here — those migrations are tracked by later stages.

## References

* `references/ldt-paper/test_definition.tex`, `def:general-projective-strategy`
* `blueprint/src/chapter/ch02_test.tex`
* `docs/scouting/ch02_separate_local_spaces.md`
-/

namespace MIPStarRE.LDT

open scoped BigOperators MatrixOrder Matrix ComplexOrder

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
