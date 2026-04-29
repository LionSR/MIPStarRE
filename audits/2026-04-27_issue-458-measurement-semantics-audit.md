---
title: "Issue 458 measurement-semantics audit"
date: 2026-04-27
purpose: >
  Audit of measurement and submeasurement semantics for issue #458, comparing the paper definitions with Lean structures.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Issue #458 measurement-semantics audit

Date: 2026-04-27
Branch: `gpt55/issue-458-session32`

## Paper anchor

`references/ldt-paper/preliminaries.tex:127--137` distinguishes the two notions:

- a **sub-measurement** is a PSD family with $\sum_a A_a \le I$;
- a **measurement** is the stronger POVM case $\sum_a A_a = I$.

`references/ldt-paper/preliminaries.tex:169--180` then states that postprocessing preserves both
sub-measurements and measurements.

## Current Lean status

- `MIPStarRE/LDT/Basic/SubMeasurementCore.lean` matches the paper-local split:
  - `SubMeas` has an explicit `total` and `total_le_one`;
  - `Measurement` extends `SubMeas` with `total_eq_one`;
  - `ProjSubMeas` / `ProjMeas` add idempotence.
- `MIPStarRE/Quantum/Measurement.lean` has the same split at the reusable quantum layer:
  - `Quantum.Submeasurement.sum_le_one` for the relaxed sub-POVM notion;
  - `Quantum.Measurement.sum_eq_one` for complete POVMs.
- The remaining #458 semantic risk is therefore call-site choice, not the existence of the
  relaxed structure itself: a paper statement that assumes a POVM should use `Measurement` /
  `ProjMeas` or supply an explicit completeness proof before promoting a `SubMeas`.

## Default-instance audit

A project-wide search for measurement/state defaults found:

- No global `Inhabited` instance for `QuantumState`, `SubMeas`, or `ProjSubMeas`.
- No global `Inhabited` instance for `Quantum.Submeasurement` or `Quantum.Measurement`.
- The only measurement-family defaults are the complete one-outcome-at-`default` witnesses:
  - `Inhabited (Measurement α ι)` in `SubMeasurementCore.lean`;
  - `Inhabited (ProjMeas α ι)` in `SubMeasurementCore.lean`.
- Explicit uses of those defaults are sparse. The notable one is the already-documented
  witness choice in `MIPStarRE/LDT/Test/MainTheorem.lean:168--193`, which uses
  `default : ProjMeas ...` only to realize an ambient witness package and is outside this
  PR's scope.

This confirms the previously merged unsafe-zero-default cleanup is still intact.

## Session32 helper additions

This PR adds small proved bridge lemmas rather than changing structure semantics:

- `MIPStarRE.LDT.SubMeas.sum_eq_one_iff_total_eq_one`
- `MIPStarRE.LDT.SubMeas.toMeasurement`
- simp lemmas for the promoted measurement's underlying submeasurement/outcomes
- `MIPStarRE.Quantum.Submeasurement.total_eq_sum`
- `MIPStarRE.Quantum.Submeasurement.total_le_one`
- `MIPStarRE.Quantum.Submeasurement.postprocess_sum_eq`
- `MIPStarRE.Quantum.Submeasurement.postprocess_total`
- `MIPStarRE.Quantum.Measurement.ofSumEqOne`
- `MIPStarRE.Quantum.Measurement.total_eq_one`
- `MIPStarRE.Quantum.Measurement.postprocess`

The intended downstream pattern is: keep relaxed submeasurements where the paper says
$\sum_a A_a \le I$, but promote explicitly to `Measurement` when a proof has established
$\sum_a A_a = I$.

## Remaining work

A full call-site audit is still needed before any structural rename such as
`Submeasurement` → `PartialPOVM`. In particular, uses under
`LDT/MakingMeasurementsProjective/`, `LDT/SelfImprovement/MatrixRealization.lean`, and
strategy/test packages should be checked against the paper to decide whether each family is
intentionally a relaxed submeasurement or should be complete.
