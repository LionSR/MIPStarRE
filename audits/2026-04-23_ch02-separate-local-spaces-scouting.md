---
title: "Separate Alice/Bob local spaces scouting"
date: 2026-04-23
purpose: >
  Scouting note for separating Alice and Bob local Hilbert spaces in Chapter 2 strategy definitions and downstream consumers.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Scouting: separate Alice/Bob local spaces for `ProjStrat`

Date: 2026-04-23
Issue: #560

> **Historical snapshot.** This note records the Session 26 scouting state on
> 2026-04-23. The coordination audit below names the then-open PR queue; use
> the live GitHub PR list, not those PR numbers, for current collision checks.

## Scope read

Paper:

- `references/ldt-paper/test_definition.tex:79-115`

Lean:

- `MIPStarRE/LDT/Test/StrategyCore.lean`
- `MIPStarRE/LDT/Test/StrategyRole.lean`
- `MIPStarRE/LDT/Test/SymmetrizationBridge.lean`
- `MIPStarRE/LDT/Test/StrategyRoleAverage.lean`
- `MIPStarRE/LDT/Test/StrategySelfConsistency.lean`
- `MIPStarRE/LDT/Test/StrategyFailures.lean`
- `MIPStarRE/LDT/Test/MainTheorem.lean`
- `MIPStarRE/LDT/CommutativityPoints/Defs.lean`
- `MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean`
- `MIPStarRE/LDT/MainInductionStep/Defs.lean`
- `MIPStarRE/LDT/MainInductionStep/Statements.lean`
- `MIPStarRE/LDT/MainInductionStep/Theorems.lean`

Coordination audit (2026-04-23 snapshot):

- Then-open PR #641 touched `MIPStarRE/LDT/Test/StrategyFailures.lean`
- Then-open PRs #646 and #649 touched `MIPStarRE/LDT/Test/MainTheorem.lean`
- Then-open PRs #645 and #649 touched `MIPStarRE/LDT/MainInductionStep/*`
- Then-open PRs #609 and #620 touched `MIPStarRE/LDT/Commutativity/*`

## Executive summary

The paper's general projective strategy is genuinely two-space:
`test_definition.tex:98-115` uses a bipartite state
$\ket{\psi} \in \mathcal H_{\mathrm A} \otimes \mathcal H_{\mathrm B}$,
with Alice's measurements acting on $\mathcal H_{\mathrm A}$ and Bob's on
$\mathcal H_{\mathrm B}$.

The current Lean `ProjStrat` is not just paper-inexact at the outer container.
It is embedded in a broader same-space architecture:

1. `swapDensity` and `PermInvState` are defined only on `ι × ι`.
2. `SymStrat` and `ProjStrat` both use a single local index type `ι`.
3. Role-register symmetrization targets `SymStrat params (Role × ι)`.
4. Section 8 (`CommutativityPoints/*`) and Section 10 (`MainInductionStep/*`)
   consume the same-space `SymStrat` API downstream.

Because that open PR set overlapped the `ProjStrat` consumers for paper statements
(`StrategyFailures.lean`, `MainTheorem.lean`) and the deepest symmetrized
downstream (`MainInductionStep/*`, `Commutativity/*`), an end-to-end refactor
was not safe to land in Session 26 without colliding with in-flight work. The
safe outcome for that session was therefore **scouting only**.

## Paper / Lean mismatch

### Paper definition

`references/ldt-paper/test_definition.tex:98-115`:

- state: $\ket{\psi} \in \mathcal H_{\mathrm A} \otimes \mathcal H_{\mathrm B}$
- Alice measurements act on $\mathcal H_{\mathrm A}$
- Bob measurements act on $\mathcal H_{\mathrm B}$
- no same-space assumption is built into the general strategy container

### Current Lean definition

`MIPStarRE/LDT/Test/StrategyCore.lean:377-388`:

```lean
structure ProjStrat (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  state : QuantumState (ι × ι)
  permInvState : PermInvState state
  densityFixed : swapDensity state.density = state.density
  isNormalized : state.IsNormalized
  pointMeasurementA : IdxProjMeas ... ι
  axisParallelMeasurementA : ... ι
  diagonalMeasurementA : ... ι
  pointMeasurementB : IdxProjMeas ... ι
  axisParallelMeasurementB : ... ι
  diagonalMeasurementB : ... ι
```

So Lean currently bakes in **three** stronger assumptions than the paper's
`def:projective-strategy`:

- common local carrier `ι`
- common bipartite space `ι × ι`
- built-in swap symmetry data (`permInvState`, `densityFixed`)

The grep audit requested in the session setup also found **no existing**
`aliceSpace`, `bobSpace`, or `localSpace` fields in `LDT/Test`; the current API
is entirely type-parameter based, not record-field based.

## Current same-space anchors

### 1. `swapDensity` / `PermInvState` are homogeneous by construction

`MIPStarRE/LDT/Test/StrategyCore.lean:18-40`:

- `swapDensity` is defined only for operators on `(ι × ι)`.
- `PermInvState` is defined only for `QuantumState (ι × ι)`.
- `swap_ev` compares `leftTensor` and `rightTensor` of operators on the **same** local type `ι`.

This means a naive change from `ProjStrat params ι` to
`ProjStrat params ιA ιB` does not just require changing binders. It also forces a
choice about what replaces the current same-space swap infrastructure.

### 2. `SymStrat` is also same-space

`MIPStarRE/LDT/Test/StrategyCore.lean:241-249`:

```lean
structure SymStrat ... (ι : Type*) ... where
  state : QuantumState (ι × ι)
  permInvState : PermInvState state
  densityFixed : swapDensity state.density = state.density
  ...
```

So even if `ProjStrat` were generalized, the current downstream target remains a
same-space symmetric strategy.

### 3. Role-register symmetrization uses `Role × ι`, not a true direct sum of two spaces

`MIPStarRE/LDT/Test/StrategyRole.lean:55-58`, `102-126`, `233-245`, `864-913`:

- `roleCond` maps an operator on `ι` to one on `Role × ι`
- `rolePairPayloadEquiv` reindexes `((Role × Role) × (ι × ι))`
  into `((Role × ι) × (Role × ι))`
- `classicalRoleSymmState` places the original and swapped states into the
  `A/B` and `B/A` role sectors of a space built from the **same payload** `ι`
- `classicalRoleSymmStrategy` packages the result as `SymStrat params (Role × ι)`

This is exactly the issue description's warning: the current symmetrization is a
same-index block-diagonal construction, not a general direct-sum construction for
possibly different payloads.

### 4. Public bridge fixes the same-space target in the API

`MIPStarRE/LDT/Test/SymmetrizationBridge.lean:72-76`:

```lean
noncomputable abbrev strategySymmetrization ...
    (strategy : ProjStrat params ι) :
    SymStrat params (Role × ι)
```

Any paper-faithful two-space `ProjStrat` must either:

- replace this bridge with a direct-sum target such as `Sum ιA ιB`, or
- leave the existing same-space `ProjStrat → SymStrat` pipeline in place and
  introduce a parallel paper-faithful container alongside it.

## Downstream consumer audit

### Direct `ProjStrat` consumers inside `LDT/Test`

These files would need signature changes if `ProjStrat` itself changed arity:

- `MIPStarRE/LDT/Test/StrategyRole.lean:866-919`
- `MIPStarRE/LDT/Test/StrategyRoleAverage.lean:267-489`
- `MIPStarRE/LDT/Test/StrategySelfConsistency.lean:39-176`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:81-259`
- `MIPStarRE/LDT/Test/SymmetrizationBridge.lean:72-116`
- `MIPStarRE/LDT/Test/MainTheorem.lean:161-182`

Important note: a repository-wide grep found **no** `ProjStrat.mk` uses and no
record literals constructing `ProjStrat` under `MIPStarRE/`. The refactor cost is
therefore concentrated at binder/projection sites, not at many constructor call
sites.

### `SymStrat`-only downstream consumers

These do not mention `ProjStrat` directly, but they depend on the current
same-space symmetric API and therefore constrain any refactor of the
`ProjStrat → SymStrat` bridge.

#### `CommutativityPoints/*`

Examples:

- `MIPStarRE/LDT/CommutativityPoints/Defs.lean:168-176`
- `MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean:214-364`

The API there is uniformly of the form `strategy : SymStrat params ι`, and many
definitions explicitly build operators on the bipartite space `ι × ι`. For
example, `pointMeasurementProductLeft` returns an operator family on `ι × ι`.

#### `MainInductionStep/*`

Examples:

- `MIPStarRE/LDT/MainInductionStep/Defs.lean:301-320`
- `MIPStarRE/LDT/MainInductionStep/Statements.lean:33-337`
- `MIPStarRE/LDT/MainInductionStep/Theorems.lean:39-2590`

The induction chapter is also uniformly written over `SymStrat params ι`. In
particular, `xRestrictedStrategy` (`Defs.lean:311-320`) restricts a symmetric
strategy while reusing the same bipartite state.

### Conclusion of the audit

A two-space projective strategy can be introduced without touching
`CommutativityPoints/*` or `MainInductionStep/*` **only if** the current
same-space `SymStrat` API remains intact and the paper-faithful two-space
container lives alongside it. Once the goal becomes to make `mainFormal`
paper-faithful at its outermost strategy argument, the refactor inevitably
reaches the current bridge and therefore the then-open PR files below.

## Historical open-PR overlap audit

The Session 26 pass was explicitly constrained not to touch the then-active
open-PR files. Relevant overlaps were:

- PR #641 modified `MIPStarRE/LDT/Test/StrategyFailures.lean`
- PR #646 modified `MIPStarRE/LDT/Test/MainTheorem.lean`
- PR #649 modified `MIPStarRE/LDT/Test/MainTheorem.lean` and
  `MIPStarRE/LDT/MainInductionStep/Theorems.lean`
- PR #645 modified `MIPStarRE/LDT/MainInductionStep/*`
- PRs #609 and #620 modified `MIPStarRE/LDT/Commutativity/*`

Therefore, the files most likely to be touched by a paper-faithful `ProjStrat`
refactor were precisely the files that were unsafe to edit in that session.

## Minimal API surface for a future refactor

The smallest paper-faithful addition that matches the current codebase style is
**not** to add `aliceSpace` / `bobSpace` record fields. `LDT/Test` does not use
`FiniteHilbertSpace`-valued fields at all; it uses local carrier types directly.
So the minimal future container should be type-parameter based:

```lean
structure BiProjStrat (params : Parameters) [FieldModel params.q]
    (ιA : Type*) [Fintype ιA] [DecidableEq ιA]
    (ιB : Type*) [Fintype ιB] [DecidableEq ιB] where
  state : QuantumState (ιA × ιB)
  isNormalized : state.IsNormalized
  pointMeasurementA : IdxProjMeas (Point params) (Fq params) ιA
  axisParallelMeasurementA : AxisParallelCovariantMeasurement params ιA
  diagonalMeasurementA : DiagonalCovariantMeasurement params ιA
  pointMeasurementB : IdxProjMeas (Point params) (Fq params) ιB
  axisParallelMeasurementB : AxisParallelCovariantMeasurement params ιB
  diagonalMeasurementB : DiagonalCovariantMeasurement params ιB
```

Then keep the current same-space `ProjStrat` as the symmetrizable special case,
for example by leaving it unchanged for now or later renaming it to something
like `SameSpaceProjStrat`.

## What the follow-up refactor would need

### Stage 1: introduce the paper-faithful two-space container

- Add `BiProjStrat params ιA ιB` in `StrategyCore.lean` (or a sibling file).
- Add the obvious forgetful map from current same-space `ProjStrat params ι` to
  `BiProjStrat params ι ι`.
- Do **not** yet change `StrategyFailures.lean` or `MainTheorem.lean` while that
  Session 26 PR stack is open.

### Stage 2: build a true direct-sum role symmetrization

The present target `Role × ι` must be replaced, for heterogeneous local spaces,
by a genuine tagged sum such as `Sum ιA ιB` (or an equivalent sigma type).

That stage needs:

- embeddings of Alice/Bob local operators into the corresponding direct-sum blocks
- a bipartite direct-sum state on `(Sum ιA ιB) × (Sum ιA ιB)`
- proofs that the new state is normalized and swap-invariant
- heterogeneous analogues of the current block-diagonal symmetrization lemmas

Only after that can one define a paper-faithful bridge
`BiProjStrat params ιA ιB → SymStrat params (Sum ιA ιB)`.

### Stage 3: migrate theorem statements from the paper

After the relevant downstream PR stack clears, update:

- `StrategyFailures.lowIndividualDegreeFailureProbability`
- `ProjStrat.PassesLowIndividualDegreeTest`
- `SymmetrizationBridge.strategySymmetrization`
- `MainTheorem.mainFormal`

At that point `blueprint/src/chapter/ch02_test.tex` can restore `\leanok` for
`def:projective-strategy`.

## Recommendation

Do **not** attempt the full refactor on top of that historical open PR set.

Recommended next implementation branch after the then-stacked PRs merge:

1. introduce `BiProjStrat` only;
2. prove a direct-sum symmetrization bridge in fresh non-overlapping files;
3. then retarget `StrategyFailures` and `MainTheorem`.

That staged plan keeps Section 8 / Section 10 stable until the new bridge exists,
which is the narrowest path to a paper-faithful `ProjStrat` without disrupting the
same-space `SymStrat` pipeline already used downstream.
