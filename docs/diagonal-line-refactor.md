# Diagonal-line rebasing refactor plan

Issue: #529  
Related PRs: #520, #371

## Verdict

This change takes **Option B** (explicit measurement transport), but in a
**scouting-first** form.

A quotient-based redesign of `DiagonalLine` would require a broad reindexing
pass across many files:

- `LDT/Basic/`
- `LDT/Test/`
- `LDT/MainInductionStep/`
- `LDT/CommutativityPoints/`

The scouting pass found well over ten live `DiagonalLine` consumers, plus the
same parametrized-line phenomenon for `AxisParallelLine`. So the first useful
step is to make the transport API explicit and reusable before changing the
strategy structures.

## What lands in this PR

1. **Outcome transport for measurements along an equivalence**
   - `SubMeas.transport`
   - `Measurement.transport`
   - `ProjSubMeas.transport`
   - `ProjMeas.transport`
   - `SubMeas.postprocess_transport`

2. **Answer-side rebasing equivalences**
   - `AxisLinePolynomial.reparamAtEquiv`
   - `DiagonalLinePolynomial.reparamAtEquiv`

3. **Question-side measurement transport helpers**
   - `AxisParallelLine.transportMeasurement`
   - `DiagonalLine.transportMeasurement`

4. **Stronger transport-level invariance predicates**
   - `AxisParallelMeasurementTransportInvariant`
   - `DiagonalMeasurementTransportInvariant`

   Each stronger predicate implies the existing evaluation-level predicate:
   - `AxisParallelMeasurementTransportInvariant.toEvaluationReparamInvariant`
   - `DiagonalMeasurementTransportInvariant.toEvaluationReparamInvariant`

## Why this is the right intermediate API

The old predicates only say that two **postprocessed** measurements agree after
reading answers at `0` versus at the rebasing parameter $t$. They do **not**
identify the underlying projective measurement outcome-by-outcome.

The new transport API records the stronger statement that the rebased question
literally carries the transported measurement:

$$
M(\operatorname{rebaseAt}(\ell,t))
  = \operatorname{transportMeasurement}(M(\ell), t).
$$

That is the form needed for a future covariant-wrapper API.

## Planned follow-up migration

A follow-up PR can now replace the raw fields

- `SymStrat.axisParallelMeasurement`
- `SymStrat.diagonalMeasurement`
- `ProjStrat.axisParallelMeasurementA/B`
- `ProjStrat.diagonalMeasurementA/B`

with covariant measurement wrappers that package

- the indexed projective measurement family, and
- the corresponding transport-fixed-point law.

At that point, the standalone structural fields

- `axisParallelReparamInvariant`
- `diagonalReparamInvariant`
- `axisParallelReparamInvariantA/B`
- `diagonalReparamInvariantA/B`

can be deleted, and theorem statements such as `commutativityPoints` will no
longer mention separate rebasing hypotheses.

## Non-goals of this PR

- No quotient of `DiagonalLine`
- No mass rewrite of question products such as `DiagonalLine params × Fq params`
- No theorem statement churn in `SymStrat`, `ProjStrat`, or `commutativityPoints`

This keeps the foundational change reviewable while making the next migration
mechanical rather than speculative.
