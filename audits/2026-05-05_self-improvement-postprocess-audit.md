---
title: Self-improvement postprocess identity audit
date: 2026-05-05
purpose: >
  Records the post-merge audit requested by issue #1114 for the
  identity-postprocessing cleanup in the self-improvement files.
status: resolved
track: paper2009ldt
kind: proof-infrastructure-audit
origin: "issue #1114"
issue: "#1114"
pr: "#1280"
---

# Self-Improvement Postprocess Identity Audit

## Scope

The audit covered the self-improvement development and the measurement
infrastructure that supplies the shared postprocessing lemmas:

- `MIPStarRE/LDT/SelfImprovement/`
- `MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean`
- `MIPStarRE/Quantum/Measurement.lean`

The search terms were chosen to find both direct uses of the shared API and
possible local repetitions of the identity-postprocessing argument:

```bash
rg -n "postprocess_id|postprocess_outcome|postprocess id|postprocess.*id|SubMeas.postprocess" \
  MIPStarRE/LDT/SelfImprovement MIPStarRE/LDT/Basic MIPStarRE/Quantum
```

## Source of Truth

The relevant shared API is the submeasurement postprocessing API in
`MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean`:

- `SubMeas.postprocess_outcome`
- `SubMeas.postprocess_id`

Issue #1114 asked that self-improvement proofs use these shared lemmas instead
of repeating the finite-fiber calculation for identity postprocessing.

## Findings

The only self-improvement call site found by the audit is the private lemma
`polynomialEvaluationFamily_outcome_eq_fiber_sum`, currently in
`MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness.lean`.
That proof rewrites the evaluated polynomial family by
`SubMeas.postprocess_outcome`.

No local proof of identity postprocessing was found in the self-improvement
files. In particular, the previous pattern of reproving the fiber of an
identity postprocess has not reappeared after the helper-completeness and
add-in-u refactors.

## Required Action

No further action is required for the audited scope. The postprocess identity
cleanup requested by issue #1114 is closed for the self-improvement files.

## Validation

The audit used the `rg` invocation displayed in the `Scope` section. The PR
which records this audit also validated the touched self-improvement module by
building `MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep34AndTransfer`
and checking the blueprint declaration list.

## Review Use

Future self-improvement proofs that evaluate a postprocessed submeasurement
should use `SubMeas.postprocess_outcome`. The special case of the identity map
should use `SubMeas.postprocess_id` rather than unfolding the finite-fiber
definition.
