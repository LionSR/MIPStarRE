# Diagonal-line rebasing refactor status

Issue: #529  
Related PRs: #371, #520, #548, #574

## Verdict

Issue #529 is now complete on `main`.

The repository took **Option B** (explicit measurement transport with
transport-covariant wrappers), not the quotient redesign of `DiagonalLine`.
The work landed in two merged PRs:

1. **#548** — added the reusable measurement-transport scaffolding.
2. **#574** — migrated `SymStrat` / `ProjStrat` to covariant wrappers and
   removed the standalone rebasing-invariance fields.

This document is now a status record of that design choice, rather than a
forward-looking migration plan.

## Why the quotient route was not taken

A quotient-based redesign of `DiagonalLine` would have forced a much broader
reindexing sweep through many live consumers across:

- `LDT/Basic/`
- `LDT/Test/`
- `LDT/MainInductionStep/`
- `LDT/CommutativityPoints/`

The same parametrized-line phenomenon also appears for `AxisParallelLine`, so a
scouting pass favored making the transport API explicit first and then bundling
covariance into the measurement types.

## What landed

### 1. Outcome transport along equivalences

The reusable transport layer now includes:

- `SubMeas.transport`
- `Measurement.transport`
- `ProjSubMeas.transport`
- `ProjMeas.transport`
- `SubMeas.postprocess_transport`

### 2. Answer-side rebasing equivalences

The answer types now expose rebasing equivalences:

- `AxisLinePolynomial.reparamAtEquiv`
- `DiagonalLinePolynomial.reparamAtEquiv`

### 3. Question-side transport helpers

Line-indexed measurements can be transported directly along rebasing via:

- `AxisParallelLine.transportMeasurement`
- `DiagonalLine.transportMeasurement`

### 4. Transport-level covariance predicates and wrappers

The stronger transport-fixed-point laws are:

- `AxisParallelMeasurementTransportInvariant`
- `DiagonalMeasurementTransportInvariant`

These are bundled into the wrapper types:

- `AxisParallelCovariantMeasurement`
- `DiagonalCovariantMeasurement`

The line-measurement fields of `SymStrat` and `ProjStrat` now use those wrapper
structures directly.

### 5. Derived evaluation-level invariance lemmas

The older evaluation-at-`zeroCoord` predicates remain available as derived
consequences:

- `AxisParallelMeasurementTransportInvariant.toEvaluationReparamInvariant`
- `DiagonalMeasurementTransportInvariant.toEvaluationReparamInvariant`
- `AxisParallelCovariantMeasurement.reparamInvariant`
- `DiagonalCovariantMeasurement.reparamInvariant`

## Statement-level outcome

The follow-up migration promised by the original scouting note has already
landed.

In particular:

- `SymStrat` and `ProjStrat` no longer carry standalone
  `axisParallelReparamInvariant*` / `diagonalReparamInvariant*` fields.
- `AxisParallelLine` and `DiagonalLine` are treated in parallel under the same
  transport-covariant pattern.
- `SymStrat.IsGood` now contains exactly the three paper-facing goodness bounds:
  `axisParallelTest`, `selfConsistencyTest`, and `diagonalLineTest`.
- The Lean entry point `commutativityPoints` now has the intended paper-faithful
  hypothesis shape: the rebasing covariance is structural data inside the
  strategy, not an extra theorem argument.

## Historical note

Issue #529 began as a design question about how to make diagonal-line
reparametrization invariance part of the API rather than an external predicate.
The current repository answer is:

- keep the concrete line types,
- make rebasing transport explicit,
- package covariance with the measurement families, and
- recover the older evaluation-level formulas as lemmas when needed.

That staging avoided a quotient-heavy rewrite while still eliminating the stale
statement-level mismatch that motivated the issue.
