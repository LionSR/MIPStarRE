# Self-improvement postprocess identity audit

Date: 2026-05-05.

This note records the post-merge audit requested by issue #1114 for the
identity-postprocessing cleanup in the self-improvement files.  The purpose of
the audit is to check that no local proof of identity postprocessing remains
where the shared `SubMeas.postprocess_id` and `SubMeas.postprocess_outcome`
lemmas should now be used.

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

## Findings

The shared submeasurement lemmas are present in
`MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean`:

- `SubMeas.postprocess_outcome`
- `SubMeas.postprocess_id`

The only self-improvement call site found by the audit is
`polynomialEvaluationFamily_apply` in
`MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness.lean`,
which already rewrites by `SubMeas.postprocess_outcome`.

No local proof of identity postprocessing was found in the self-improvement
files.  In particular, the previous pattern of reproving the fiber of an
identity postprocess has not reappeared after the helper-completeness and
add-in-u refactors.

## Verdict

The postprocess identity cleanup is complete for the self-improvement scope.
Future self-improvement proofs that evaluate a postprocessed submeasurement
should use `SubMeas.postprocess_outcome`; the special case of the identity map
should use `SubMeas.postprocess_id` rather than unfolding the finite fiber
definition.
